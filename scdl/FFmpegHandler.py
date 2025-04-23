import io
import logging
import shutil
import subprocess
import tempfile
import threading
from typing import List, Set, Union, Optional

from tqdm import tqdm

logger = logging.getLogger(__name__)

FFMPEG_PIPE_CHUNK_SIZE = 1024 * 1024  # 1 mb

class FFmpegHandler:
    def __init__(self, debug: bool = False, hide_progress: bool = False):
        """Initialize FFmpegHandler with configuration."""
        self.debug = debug
        self.hide_progress = hide_progress
        self.supported_options = self._get_ffmpeg_supported_options()

    def build_ffmpeg_encoding_args(
        self,
        input_file: str,
        output_file: str,
        out_codec: str,
        extra_args: List[str] = None
    ) -> List[str]:
        """Build FFmpeg command-line arguments."""
        ffmpeg_args = [
            "ffmpeg",
            "-loglevel",
            "debug" if self.debug else "error",
            "-i",
            input_file,
            "-f",
            out_codec,
        ]

        if not self.hide_progress:
            ffmpeg_args += ["-progress", "pipe:2"]
            if "-stats_period" in self.supported_options:
                ffmpeg_args += ["-stats_period", "0.1"]

        if extra_args:
            ffmpeg_args += extra_args

        ffmpeg_args.append(output_file)
        return ffmpeg_args

    def _get_ffmpeg_pipe(
        self,
        in_data: Union[str, io.BytesIO],
        out_codec: str,
        should_copy: bool,
        output_file: str
    ) -> subprocess.Popen:
        """Create an FFmpeg subprocess pipe."""
        commands = self.build_ffmpeg_encoding_args(
            in_data if isinstance(in_data, str) else "-",
            output_file,
            out_codec,
            ["-c", "copy"] if should_copy else []
        )
        logger.debug(f"ffmpeg command: {' '.join(commands)}")
        return subprocess.Popen(
            commands,
            stdin=subprocess.PIPE,
            stderr=subprocess.PIPE,
            stdout=subprocess.PIPE,
            bufsize=FFMPEG_PIPE_CHUNK_SIZE,
        )

    def _is_ffmpeg_progress_line(self, parameters: List[str]) -> bool:
        """Check if a line is an FFmpeg progress line."""
        return len(parameters) == 2 and parameters[0] in (
            "progress", "speed", "drop_frames", "dup_frames",
            "out_time", "out_time_ms", "out_time_us", "total_size", "bitrate"
        )

    def _is_unsupported_codec_for_streaming(self, codec: str) -> bool:
        """Check if codec is unsupported for streaming."""
        return codec in ("ipod", "flac")

    def re_encode(
        self,
        in_data: Union[requests.Response, str, io.BytesIO],
        out_codec: str,
        should_copy: bool,
        track_duration_ms: int,
        output_file: Optional[str] = None
    ) -> io.BytesIO:
        """Encode input data using FFmpeg and return the encoded stream."""
        logger.info("Encoding...")
        errors_output = ""
        stdout = io.BytesIO()

        streaming_supported = not self._is_unsupported_codec_for_streaming(out_codec)
        out_file_name = output_file or "pipe:1"

        if not streaming_supported and not output_file:
            temp_dir = tempfile.TemporaryDirectory()
            out_file_name = str(pathlib.Path(temp_dir.name) / "scdl")
        else:
            temp_dir = None

        pipe = self._get_ffmpeg_pipe(in_data, out_codec, should_copy, out_file_name)

        def read_stdout() -> None:
            assert pipe.stdout is not None
            shutil.copyfileobj(pipe.stdout, stdout, FFMPEG_PIPE_CHUNK_SIZE)
            pipe.stdout.close()

        stdout_thread = None
        stdin_thread = None

        if out_file_name == "pipe:1":
            stdout_thread = threading.Thread(target=read_stdout, daemon=True)

        if isinstance(in_data, requests.Response):
            assert pipe.stdin is not None
            stdin_thread = threading.Thread(
                target=self._write_streaming_response_to_pipe,
                args=(in_data, pipe.stdin),
                daemon=True,
            )
        elif isinstance(in_data, io.BytesIO):
            assert pipe.stdin is not None
            stdin_thread = threading.Thread(
                target=shutil.copyfileobj,
                args=(in_data, pipe.stdin, FFMPEG_PIPE_CHUNK_SIZE),
                daemon=True,
            )

        if stdout_thread:
            stdout_thread.start()
        if stdin_thread:
            stdin_thread.start()

        hide_progress = self.hide_progress
        total_sec = track_duration_ms / 1000
        with tqdm(total=total_sec, disable=hide_progress, unit="s") as progress:
            last_secs = 0.0
            assert pipe.stderr is not None
            for line in io.TextIOWrapper(pipe.stderr, encoding="utf-8", errors=None):
                parameters = line.split("=", maxsplit=1)
                if hide_progress or not self._is_ffmpeg_progress_line(parameters):
                    errors_output += line
                    continue
                if not line.startswith("out_time_ms"):
                    continue
                try:
                    seconds = int(parameters[1]) / 1_000_000
                except ValueError:
                    seconds = 0.0
                seconds = min(seconds, total_sec)
                changed = seconds - last_secs
                last_secs = seconds
                progress.update(changed)

        if stdout_thread:
            stdout_thread.join()
        if stdin_thread:
            stdin_thread.join()

        logger.debug(f"FFmpeg output: {errors_output}")

        pipe.wait()
        if pipe.returncode != 0:
            raise FFmpegError(pipe.returncode, errors_output)

        if out_file_name != "pipe:1":
            with open(out_file_name, "rb") as f:
                shutil.copyfileobj(f, stdout)

        stdout.seek(0)

        if temp_dir:
            temp_dir.cleanup()

        return stdout

    def _write_streaming_response_to_pipe(
        self,
        response: requests.Response,
        pipe: Union[io.BufferedWriter, io.BytesIO]
    ) -> None:
        """Write streaming response to FFmpeg pipe."""
        total_length = int(response.headers["content-length"])
        logger.info("Receiving the streaming response")
        received = 0
        chunk_size = 8192

        with memoryview(bytearray(chunk_size)) as buffer:
            for chunk in tqdm(
                iter(lambda: response.raw.read(chunk_size), b""),
                total=(total_length / chunk_size) + 1,
                disable=self.hide_progress,
                unit="Kb",
                unit_scale=chunk_size / 1024,
            ):
                if not chunk:
                    break
                buffer_view = buffer[:len(chunk)]
                buffer_view[:] = chunk
                received += len(chunk)
                pipe.write(buffer_view)

        pipe.flush()

        if received != total_length:
            logger.error("connection closed prematurely, download incomplete")
            sys.exit(1)

        if not isinstance(pipe, io.BytesIO):
            pipe.close()

    def copy_stream(self, in_data: requests.Response) -> io.BytesIO:
        """Copy streaming response to a BytesIO buffer without encoding."""
        result = io.BytesIO()
        self._write_streaming_response_to_pipe(in_data, result)
        result.seek(0)
        return result

    def _get_ffmpeg_supported_options(self) -> Set[str]:
        """Return supported FFmpeg options."""
        if shutil.which("ffmpeg") is None:
            logger.error("ffmpeg is not installed")
            sys.exit(1)
        r = subprocess.run(
            ["ffmpeg", "-help", "long", "-loglevel", "quite"],
            check=True,
            stdout=subprocess.PIPE,
            encoding="utf-8",
        )
        supported = set()
        for line in r.stdout.splitlines():
            if line.startswith("-"):
                opt = line.split(maxsplit=1)[0]
                supported.add(opt)
        return supported
