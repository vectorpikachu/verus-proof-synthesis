"""
This file contains the main interface and the public API for multilspy. 
The abstract class LanguageServer provides a factory method, creator that is 
intended for creating instantiations of language specific clients.
The details of Language Specific configuration are not exposed to the user.
"""

import asyncio
import dataclasses
import json
from pprint import pprint
import shutil
import time
import logging
import os
import pathlib
import threading
from contextlib import asynccontextmanager, contextmanager

import aiofiles
from .lsp_protocol_handler.lsp_constants import LSPConstants
from .lsp_protocol_handler import lsp_types as LSPTypes

from . import multilspy_types
from .multilspy_logger import MultilspyLogger
from .lsp_protocol_handler.server import (
    LanguageServerHandler,
    ProcessLaunchInfo,
)
from .multilspy_config import MultilspyConfig, Language
from .multilspy_exceptions import MultilspyException
from .multilspy_utils import PathUtils, FileUtils, TextUtils
from pathlib import PurePath
from typing import AsyncIterator, Iterator, List, Dict, Optional, Union, Tuple
from .type_helpers import ensure_all_methods_implemented

def uri_to_path(uri: str) -> str:
    """将 file URI 转换为本地文件路径"""
    if uri.startswith("file://"):
        return uri[7:]
    return uri

@dataclasses.dataclass
class LSPFileBuffer:
    """
    This class is used to store the contents of an open LSP file in memory.
    """

    # uri of the file
    uri: str

    # The contents of the file
    contents: str

    # The version of the file
    version: int

    # The language id of the file
    language_id: str

    # reference count of the file
    ref_count: int


class LanguageServer:
    """
    The LanguageServer class provides a language agnostic interface to the Language Server Protocol.
    It is used to communicate with Language Servers of different programming languages.
    """

    @classmethod
    def create(cls, config: MultilspyConfig, logger: MultilspyLogger, repository_root_path: str) -> "LanguageServer":
        """
        Creates a language specific LanguageServer instance based on the given configuration, and appropriate settings for the programming language.

        If language is Java, then ensure that jdk-17.0.6 or higher is installed, `java` is in PATH, and JAVA_HOME is set to the installation directory.
        If language is JS/TS, then ensure that node (v18.16.0 or higher) is installed and in PATH.

        :param repository_root_path: The root path of the repository.
        :param config: The Multilspy configuration.
        :param logger: The logger to use.

        :return LanguageServer: A language specific LanguageServer instance.
        """
        if config.code_language == Language.PYTHON:
            from multilspy.language_servers.jedi_language_server.jedi_server import (
                JediServer,
            )

            return JediServer(config, logger, repository_root_path)
        elif config.code_language == Language.JAVA:
            from multilspy.language_servers.eclipse_jdtls.eclipse_jdtls import (
                EclipseJDTLS,
            )

            return EclipseJDTLS(config, logger, repository_root_path)
        elif config.code_language == Language.KOTLIN:
            from multilspy.language_servers.kotlin_language_server.kotlin_language_server import (
                KotlinLanguageServer,
            )

            return KotlinLanguageServer(config, logger, repository_root_path)
        elif config.code_language == Language.RUST:
            from multilspy.language_servers.rust_analyzer.rust_analyzer import (
                RustAnalyzer,
            )

            return RustAnalyzer(config, logger, repository_root_path)
        elif config.code_language == Language.CSHARP:
            from multilspy.language_servers.omnisharp.omnisharp import OmniSharp

            return OmniSharp(config, logger, repository_root_path)
        elif config.code_language in [Language.TYPESCRIPT, Language.JAVASCRIPT]:
            from multilspy.language_servers.typescript_language_server.typescript_language_server import (
                TypeScriptLanguageServer,
            )
            return TypeScriptLanguageServer(config, logger, repository_root_path)
        elif config.code_language == Language.GO:
            from multilspy.language_servers.gopls.gopls import Gopls

            return Gopls(config, logger, repository_root_path)
        elif config.code_language == Language.RUBY:
            from multilspy.language_servers.solargraph.solargraph import Solargraph

            return Solargraph(config, logger, repository_root_path)
        elif config.code_language == Language.DART:
            from multilspy.language_servers.dart_language_server.dart_language_server import DartLanguageServer

            return DartLanguageServer(config, logger, repository_root_path)
        elif config.code_language == Language.CPP:
            from multilspy.language_servers.clangd_language_server.clangd_language_server import ClangdLanguageServer

            return ClangdLanguageServer(config, logger, repository_root_path)
        else:
            logger.log(f"Language {config.code_language} is not supported", logging.ERROR)
            raise MultilspyException(f"Language {config.code_language} is not supported")

    def __init__(
        self,
        config: MultilspyConfig,
        logger: MultilspyLogger,
        repository_root_path: str,
        process_launch_info: ProcessLaunchInfo,
        language_id: str,
    ):
        """
        Initializes a LanguageServer instance.

        Do not instantiate this class directly. Use `LanguageServer.create` method instead.

        :param config: The Multilspy configuration.
        :param logger: The logger to use.
        :param repository_root_path: The root path of the repository.
        :param cmd: Each language server has a specific command used to start the server.
                    This parameter is the command to launch the language server process.
                    The command must pass appropriate flags to the binary, so that it runs in the stdio mode,
                    as opposed to HTTP, TCP modes supported by some language servers.
        """
        if type(self) == LanguageServer:
            raise MultilspyException(
                "LanguageServer is an abstract class and cannot be instantiated directly. Use LanguageServer.create method instead."
            )

        self.logger = logger
        self.server_started = False
        self.repository_root_path: str = repository_root_path
        self.completions_available = asyncio.Event()

        if config.trace_lsp_communication:

            def logging_fn(source, target, msg):
                self.logger.log(f"LSP: {source} -> {target}: {str(msg)}", logging.DEBUG)

        else:

            def logging_fn(source, target, msg):
                pass

        # cmd is obtained from the child classes, which provide the language specific command to start the language server
        # LanguageServerHandler provides the functionality to start the language server and communicate with it
        self.server: LanguageServerHandler = LanguageServerHandler(
            process_launch_info,
            logger=logging_fn,
            start_independent_lsp_process=config.start_independent_lsp_process,
        )

        self.language_id = language_id
        self.open_file_buffers: Dict[str, LSPFileBuffer] = {}

        # --------------------- MODIFICATIONS BY ME ---------------------------------
        self._diagnostics: Dict[str, List[LSPTypes.Diagnostic]] = {}
        # Simply use the type in LSPTypes, without writing in multilspytypes

    # --------------------- MODIFICATIONS BY ME ---------------------------------
    def _handle_diagnostics(self, params: Dict):
        """
        Handle the diagnostics from the Language Server.

        :param params: The parameters of diagnostics.
        """
        if "uri" in params and "diagnostics" in params:
            uri = params["uri"]
            diagnostics_list = params["diagnostics"]

            converted_diagnostics = []
            for diag in diagnostics_list:
                if "range" in diag and "message" in diag:
                    converted_diag = LSPTypes.Diagnostic(
                        range=diag["range"],
                        message=diag["message"],
                        severity=diag.get("severity"),
                        code=diag.get("code"),
                        source=diag.get("source"),
                        tags=diag.get("tags"),
                        relatedInformation=diag.get("relatedInformation")
                    )
                    converted_diagnostics.append(converted_diag)
        
            self._diagnostics[uri] = converted_diagnostics
            self.logger.log(f"Received {len(converted_diagnostics)} diagnostics for {uri}", logging.DEBUG)
    # --------------------- End MODIFICATIONS BY ME ---------------------------------

    @asynccontextmanager
    async def start_server(self) -> AsyncIterator["LanguageServer"]:
        """
        Starts the Language Server and yields the LanguageServer instance.

        Usage:
        ```
        async with lsp.start_server():
            # LanguageServer has been initialized and ready to serve requests
            await lsp.request_definition(...)
            await lsp.request_references(...)
            # Shutdown the LanguageServer on exit from scope
        # LanguageServer has been shutdown
        ```
        """

        # Register the handler of diagnostics.
        self.server.on_notification("textDocument/publishDiagnostics", self._handle_diagnostics)

        self.server_started = True
        yield self
        self.server_started = False

    async def request_diagnostics(self, relative_file_path: str) -> List[LSPTypes.Diagnostic]:
        """
        Get the diagnostics of a file (including warnings and errors).
        
        :param relative_file_path: The relative path to the file that need to be diagnosed.
        
        :return List[LSPTypes.Diagnostic]: The list of diagnostics. [] means None.
        """
        if not self.server_started:
            self.logger.log(
                "request_diagnostics called before Language Server started",
                logging.ERROR,
            )
            raise MultilspyException("Language Server not started")
        
        absolute_file_path = str(PurePath(self.repository_root_path, relative_file_path))
        uri = pathlib.Path(absolute_file_path).as_uri()
        
        file_was_closed = uri not in self.open_file_buffers
        if file_was_closed:
            with self.open_file(relative_file_path):
                self.save_file(relative_file_path)
                #! 保存一下verus才会开始报错? - 不对, 失败了
                await asyncio.sleep(10)
        
        return self._diagnostics.get(uri, [])

    async def request_code_actions(
        self, 
        relative_file_path: str, 
        range: multilspy_types.Range,
        diagnostics: Optional[List[LSPTypes.Diagnostic]] = None
    ) -> List[LSPTypes.CodeAction]:
        """
        向语言服务器发起 [textDocument/codeAction](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_codeAction) 请求，以查找文件中给定范围内可用的代码操作。
        
        代码操作可以包括诊断的快速修复、重构和其他自动编辑。
        
        :param relative_file_path: 要获取代码操作的文件的相对路径
        :param range: 文档中要获取代码操作的范围
        :param diagnostics: 可选的诊断列表，用于获取针对特定诊断的代码操作
        
        :return List[multilspy_types.CodeAction]: 可用代码操作的列表
        """
        if not self.server_started:
            self.logger.log(
                "request_code_actions called before Language Server started",
                logging.ERROR,
            )
            raise MultilspyException("Language Server not started")
        
        with self.open_file(relative_file_path):
            absolute_file_path = str(PurePath(self.repository_root_path, relative_file_path))
            uri = pathlib.Path(absolute_file_path).as_uri()
            
            # 如果没有提供诊断，使用存储的诊断
            if diagnostics is None and uri in self._diagnostics:
                # 只使用与请求范围重叠的诊断
                diagnostics = []
                for diag in self._diagnostics.get(uri, []):
                    diag_range = diag.range
                    # 检查诊断范围是否与请求范围重叠
                    if (diag_range["start"]["line"] <= range["end"]["line"] and 
                        diag_range["end"]["line"] >= range["start"]["line"]):
                        diagnostics.append(diag)
            
            # 准备代码操作请求
            params = {
                "textDocument": {"uri": uri},
                "range": range,
                "context": {
                    "diagnostics": diagnostics or []
                }
            }
            
            response = await self.server.send.code_action(params)
            
            if response is None:
                return []
            
            assert isinstance(response, list), f"Unexpected response from Language Server: {response}"
            
            result: List[LSPTypes.CodeAction] = []
            for action in response:
                # 代码操作可以作为 CodeAction 对象或 Command 返回
                if isinstance(action, dict):
                    if "command" in action and "title" in action:
                        # 这是一个 Command 对象
                        result.append(LSPTypes.CodeAction(
                            title=action["title"],
                            kind=action.get("kind"),
                            command=action,
                            edit=None
                        ))
                    else:
                        # 这是一个 CodeAction 对象
                        action = await self.server.send.resolve_code_action(action)
                        result.append(action)
            
            return result

    async def resolve_code_action(
        self,
        code_action: LSPTypes.CodeAction
    ) -> LSPTypes.CodeAction:
        """
        向语言服务器发起 [codeAction/resolve](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#codeAction_resolve) 请求，
        以解析代码操作的额外信息，如文档编辑。
        
        :param code_action: 要解析的代码操作对象
        
        :return LSPTypes.CodeAction: 解析后的代码操作对象
        """
        if not self.server_started:
            self.logger.log(
                "resolve_code_action called before Language Server started",
                logging.ERROR,
            )
            raise MultilspyException("Language Server not started")
        response = await self.server.send.resolve_code_action(code_action)

        if response is None:
            return code_action
        
        # 确保响应是一个字典
        assert isinstance(response, dict), f"Unexpected response from Language Server: {response}"
        
        # 更新代码操作对象
        return LSPTypes.CodeAction(**response)
    
    async def apply_code_action(
        self,
        code_action: LSPTypes.CodeAction
    ) -> bool:
        """
        应用给定的代码操作，执行其编辑或命令。
        
        代码操作可以包含工作区编辑（更改文件内容）或命令（由语言服务器执行）。
        本方法会根据代码操作的类型执行相应操作。
        
        :param code_action: 要应用的代码操作
        
        :return bool: 操作是否成功应用
        """
        if not self.server_started:
            self.logger.log(
                "apply_code_action called before Language Server started",
                logging.ERROR,
            )
            raise MultilspyException("Language Server not started")
        
        # 确保代码操作是完全解析的
        # 如果没有edit或command，先尝试解析
        if not ("edit" in code_action or "command" in code_action):
            code_action = await self.resolve_code_action(code_action)
        
        success = True
        
        # 应用编辑（如果存在）
        if "edit" in code_action:
            success = await self._apply_workspace_edit(code_action["edit"])
        
        # 执行命令（如果存在，且编辑成功或不存在编辑）
        if success and "command" in code_action:
            success = await self._execute_command(code_action["command"])
        
        return success

    async def _apply_workspace_edit(
        self,
        workspace_edit: LSPTypes.WorkspaceEdit
    ) -> bool:
        """
        应用工作区编辑到相应的文件。
        
        :param workspace_edit: LSP规范的WorkspaceEdit对象
        
        :return bool: 编辑是否成功应用
        """
        try:
            file_ops: List[Dict[str, str]] = []
            text_edits: Dict[str, List[LSPTypes.TextEdit]] = {}

            if "documentChanges" in workspace_edit:
                for change in workspace_edit["documentChanges"]:  # type: ignore
                    kind = change.get("kind")
                    if kind == "create":
                        file_ops.append({"kind": "create", "uri": change["uri"]})
                    elif kind == "rename":
                        file_ops.append({
                            "kind": "rename",
                            "oldUri": change["oldUri"],
                            "newUri": change["newUri"]
                        })
                    elif kind == "delete":
                        file_ops.append({"kind": "delete", "uri": change["uri"]})
                    else:
                        # TextDocumentEdit
                        uri = change["textDocument"]["uri"]
                        edits = change["edits"]
                        text_edits.setdefault(uri, []).extend(edits)
            elif "changes" in workspace_edit:
                for uri, edits in workspace_edit["changes"].items():  # type: ignore
                    text_edits.setdefault(uri, []).extend(edits)
            else:
                # Nothing to do
                return True
            
            for op in file_ops:
                kind = op["kind"]
                path = uri_to_path(op["uri"])
                if kind == "create":
                    os.makedirs(os.path.dirname(path), exist_ok=True)
                    # 异步创建空文件
                    async with aiofiles.open(path, mode="a"):
                        pass
                elif kind == "rename":
                    old_path = uri_to_path(op["oldUri"])
                    new_path = uri_to_path(op["newUri"])
                    os.makedirs(os.path.dirname(new_path), exist_ok=True)
                    # 为了保证异步上下文，这里使用线程池
                    await asyncio.get_event_loop().run_in_executor(
                        None, shutil.move, old_path, new_path
                    )
                elif kind == "delete":
                    # 使用线程池执行删除
                    await asyncio.get_event_loop().run_in_executor(
                        None,
                        lambda p=path: shutil.rmtree(p) if os.path.isdir(p) else os.remove(p)
                    )

            # 3. 再按 URI 应用文本修改
            for uri, edits in text_edits.items():
                path = uri_to_path(uri)
                # 3.1 读取文件内容
                async with aiofiles.open(path, mode="r", encoding="utf-8") as f:
                    lines = await f.readlines()

                # 3.2 逆序排序 edits，避免位置偏移
                edits_sorted = sorted(
                    edits,
                    key=lambda e: (
                        -e["range"]["start"]["line"],
                        -e["range"]["start"]["character"]
                    )
                )

                # 3.3 逐一替换
                for edit in edits_sorted:
                    start = edit["range"]["start"]
                    end = edit["range"]["end"]
                    new_text = edit["newText"]

                    # 计算替换前后的文本
                    before = "".join(lines[: start["line"]])
                    start_line = lines[start["line"]]
                    before += start_line[: start["character"]]

                    after_line = lines[end["line"]]
                    after = after_line[end["character"] :]
                    after += "".join(lines[end["line"] + 1 :])

                    updated = before + new_text + after
                    lines = updated.splitlines(keepends=True)

                # 3.4 写回文件
                async with aiofiles.open(path, mode="w", encoding="utf-8") as f:
                    await f.writelines(lines)

            return True
            
        except Exception as e:
            self.logger.error(f"ApplyWorkspaceEdit failed: {e}")
            return False

    async def _execute_command(
        self,
        command: LSPTypes.Command
    ) -> bool:
        """
        执行代码操作中的命令。
        
        :param command: LSP规范的Command对象
        
        :return bool: 命令是否成功执行
        """
        try:
            # 准备执行命令请求
            params = {
                "command": command["command"],
                "arguments": command.get("arguments", [])
            }
            
            # 发送执行命令请求
            await self.server.send.execute_command(params)
            
            return True  # 假设命令执行成功，除非有异常
        except Exception as e:
            self.logger.log(
                f"Error executing command: {e}",
                logging.ERROR,
            )
            return False

    # TODO: Add support for more LSP features

    @contextmanager
    def open_file(self, relative_file_path: str) -> Iterator[None]:
        """
        Open a file in the Language Server. This is required before making any requests to the Language Server.

        :param relative_file_path: The relative path of the file to open.
        """
        if not self.server_started:
            self.logger.log(
                "open_file called before Language Server started",
                logging.ERROR,
            )
            raise MultilspyException("Language Server not started")

        absolute_file_path = str(PurePath(self.repository_root_path, relative_file_path))
        uri = pathlib.Path(absolute_file_path).as_uri()

        if uri in self.open_file_buffers:
            assert self.open_file_buffers[uri].uri == uri
            assert self.open_file_buffers[uri].ref_count >= 1

            self.open_file_buffers[uri].ref_count += 1
            yield
            self.open_file_buffers[uri].ref_count -= 1
        else:
            contents = FileUtils.read_file(self.logger, absolute_file_path)

            version = 0
            self.open_file_buffers[uri] = LSPFileBuffer(uri, contents, version, self.language_id, 1)

            self.server.notify.did_open_text_document(
                {
                    LSPConstants.TEXT_DOCUMENT: {
                        LSPConstants.URI: uri,
                        LSPConstants.LANGUAGE_ID: self.language_id,
                        LSPConstants.VERSION: 0,
                        LSPConstants.TEXT: contents,
                    }
                }
            )
            yield
            self.open_file_buffers[uri].ref_count -= 1

        if self.open_file_buffers[uri].ref_count == 0:
            self.server.notify.did_close_text_document(
                {
                    LSPConstants.TEXT_DOCUMENT: {
                        LSPConstants.URI: uri,
                    }
                }
            )
            del self.open_file_buffers[uri]

    def save_file(self, relative_file_path: str) -> None:
        """
        Notify the Language Server that a file has been saved.
        This does write the buffer contents to disk, and sends
        a notification to the Language Server that the file was saved.

        :param relative_file_path: The relative path of the file to mark as saved.
        :raises MultilspyException: If the Language Server is not started or the file is not open.
        """
        if not self.server_started:
            self.logger.log(
                "save_file called before Language Server started",
                logging.ERROR,
            )
            raise MultilspyException("Language Server not started")

        absolute_file_path = str(PurePath(self.repository_root_path, relative_file_path))
        uri = pathlib.Path(absolute_file_path).as_uri()

        if uri not in self.open_file_buffers:
            self.logger.log(
                f"Attempted to save file that is not open: {relative_file_path}",
                logging.ERROR,
            )
            raise MultilspyException(f"File not open: {relative_file_path}")

        file_buffer = self.open_file_buffers[uri]
    
        # Write current buffer contents to disk
        try:
            with open(absolute_file_path, 'w', encoding='utf-8') as f:
                f.write(file_buffer.contents)
        except IOError as e:
            self.logger.log(
                f"Failed to save file {relative_file_path}: {str(e)}",
                logging.ERROR,
            )
            raise MultilspyException(f"Failed to save file: {str(e)}")

        # Notify language server about the save
        self.server.notify.did_save_text_document(
            {
                LSPConstants.TEXT_DOCUMENT: {
                    LSPConstants.URI: uri,
                    LSPConstants.TEXT: file_buffer.contents,
                }
            }
        )
        
        self.logger.log(
            f"Notified Language Server of save for file: {relative_file_path}",
            logging.DEBUG,
        )

    def insert_text_at_position(
        self, relative_file_path: str, line: int, column: int, text_to_be_inserted: str
    ) -> multilspy_types.Position:
        """
        Insert text at the given line and column in the given file and return 
        the updated cursor position after inserting the text.

        :param relative_file_path: The relative path of the file to open.
        :param line: The line number at which text should be inserted.
        :param column: The column number at which text should be inserted.
        :param text_to_be_inserted: The text to insert.
        """
        if not self.server_started:
            self.logger.log(
                "insert_text_at_position called before Language Server started",
                logging.ERROR,
            )
            raise MultilspyException("Language Server not started")

        absolute_file_path = str(PurePath(self.repository_root_path, relative_file_path))
        uri = pathlib.Path(absolute_file_path).as_uri()

        # Ensure the file is open
        assert uri in self.open_file_buffers

        file_buffer = self.open_file_buffers[uri]
        file_buffer.version += 1
        change_index = TextUtils.get_index_from_line_col(file_buffer.contents, line, column)
        file_buffer.contents = (
            file_buffer.contents[:change_index] + text_to_be_inserted + file_buffer.contents[change_index:]
        )
        self.server.notify.did_change_text_document(
            {
                LSPConstants.TEXT_DOCUMENT: {
                    LSPConstants.VERSION: file_buffer.version,
                    LSPConstants.URI: file_buffer.uri,
                },
                LSPConstants.CONTENT_CHANGES: [
                    {
                        LSPConstants.RANGE: {
                            "start": {"line": line, "character": column},
                            "end": {"line": line, "character": column},
                        },
                        "text": text_to_be_inserted,
                    }
                ],
            }
        )
        new_l, new_c = TextUtils.get_updated_position_from_line_and_column_and_edit(line, column, text_to_be_inserted)
        return multilspy_types.Position(line=new_l, character=new_c)

    def delete_text_between_positions(
        self,
        relative_file_path: str,
        start: multilspy_types.Position,
        end: multilspy_types.Position,
    ) -> str:
        """
        Delete text between the given start and end positions in the given file and return the deleted text.
        """
        if not self.server_started:
            self.logger.log(
                "insert_text_at_position called before Language Server started",
                logging.ERROR,
            )
            raise MultilspyException("Language Server not started")

        absolute_file_path = str(PurePath(self.repository_root_path, relative_file_path))
        uri = pathlib.Path(absolute_file_path).as_uri()

        # Ensure the file is open
        assert uri in self.open_file_buffers

        file_buffer = self.open_file_buffers[uri]
        file_buffer.version += 1
        del_start_idx = TextUtils.get_index_from_line_col(file_buffer.contents, start["line"], start["character"])
        del_end_idx = TextUtils.get_index_from_line_col(file_buffer.contents, end["line"], end["character"])
        deleted_text = file_buffer.contents[del_start_idx:del_end_idx]
        file_buffer.contents = file_buffer.contents[:del_start_idx] + file_buffer.contents[del_end_idx:]
        self.server.notify.did_change_text_document(
            {
                LSPConstants.TEXT_DOCUMENT: {
                    LSPConstants.VERSION: file_buffer.version,
                    LSPConstants.URI: file_buffer.uri,
                },
                LSPConstants.CONTENT_CHANGES: [{LSPConstants.RANGE: {"start": start, "end": end}, "text": ""}],
            }
        )
        return deleted_text

    def get_open_file_text(self, relative_file_path: str) -> str:
        """
        Get the contents of the given opened file as per the Language Server.

        :param relative_file_path: The relative path of the file to open.
        """
        if not self.server_started:
            self.logger.log(
                "get_open_file_text called before Language Server started",
                logging.ERROR,
            )
            raise MultilspyException("Language Server not started")

        absolute_file_path = str(PurePath(self.repository_root_path, relative_file_path))
        uri = pathlib.Path(absolute_file_path).as_uri()

        # Ensure the file is open
        assert uri in self.open_file_buffers

        file_buffer = self.open_file_buffers[uri]
        return file_buffer.contents

    async def request_definition(
        self, relative_file_path: str, line: int, column: int
    ) -> List[multilspy_types.Location]:
        """
        Raise a [textDocument/definition](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_definition) request to the Language Server
        for the symbol at the given line and column in the given file. Wait for the response and return the result.

        :param relative_file_path: The relative path of the file that has the symbol for which definition should be looked up
        :param line: The line number of the symbol
        :param column: The column number of the symbol

        :return List[multilspy_types.Location]: A list of locations where the symbol is defined
        """

        if not self.server_started:
            self.logger.log(
                "find_function_definition called before Language Server started",
                logging.ERROR,
            )
            raise MultilspyException("Language Server not started")

        with self.open_file(relative_file_path):
            # sending request to the language server and waiting for response
            response = await self.server.send.definition(
                {
                    LSPConstants.TEXT_DOCUMENT: {
                        LSPConstants.URI: pathlib.Path(
                            str(PurePath(self.repository_root_path, relative_file_path))
                        ).as_uri()
                    },
                    LSPConstants.POSITION: {
                        LSPConstants.LINE: line,
                        LSPConstants.CHARACTER: column,
                    },
                }
            )

        ret: List[multilspy_types.Location] = []
        if isinstance(response, list):
            # response is either of type Location[] or LocationLink[]
            for item in response:
                assert isinstance(item, dict)
                if LSPConstants.URI in item and LSPConstants.RANGE in item:
                    new_item: multilspy_types.Location = {}
                    new_item.update(item)
                    new_item["absolutePath"] = PathUtils.uri_to_path(new_item["uri"])
                    new_item["relativePath"] = PathUtils.get_relative_path(new_item["absolutePath"], self.repository_root_path)
                    ret.append(multilspy_types.Location(new_item))
                elif (
                    LSPConstants.ORIGIN_SELECTION_RANGE in item
                    and LSPConstants.TARGET_URI in item
                    and LSPConstants.TARGET_RANGE in item
                    and LSPConstants.TARGET_SELECTION_RANGE in item
                ):
                    new_item: multilspy_types.Location = {}
                    new_item["uri"] = item[LSPConstants.TARGET_URI]
                    new_item["absolutePath"] = PathUtils.uri_to_path(new_item["uri"])
                    new_item["relativePath"] = PathUtils.get_relative_path(new_item["absolutePath"], self.repository_root_path)
                    new_item["range"] = item[LSPConstants.TARGET_SELECTION_RANGE]
                    ret.append(multilspy_types.Location(**new_item))
                else:
                    assert False, f"Unexpected response from Language Server: {item}"
        elif isinstance(response, dict):
            # response is of type Location
            assert LSPConstants.URI in response
            assert LSPConstants.RANGE in response

            new_item: multilspy_types.Location = {}
            new_item.update(response)
            new_item["absolutePath"] = PathUtils.uri_to_path(new_item["uri"])
            new_item["relativePath"] = PathUtils.get_relative_path(new_item["absolutePath"], self.repository_root_path)
            ret.append(multilspy_types.Location(**new_item))
        else:
            assert False, f"Unexpected response from Language Server: {response}"

        return ret

    async def request_references(
        self, relative_file_path: str, line: int, column: int
    ) -> List[multilspy_types.Location]:
        """
        Raise a [textDocument/references](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_references) request to the Language Server
        to find references to the symbol at the given line and column in the given file. Wait for the response and return the result.

        :param relative_file_path: The relative path of the file that has the symbol for which references should be looked up
        :param line: The line number of the symbol
        :param column: The column number of the symbol

        :return List[multilspy_types.Location]: A list of locations where the symbol is referenced
        """

        if not self.server_started:
            self.logger.log(
                "find_all_callers_of_function called before Language Server started",
                logging.ERROR,
            )
            raise MultilspyException("Language Server not started")

        with self.open_file(relative_file_path):
            # sending request to the language server and waiting for response
            response = await self.server.send.references(
                {
                    "context": {"includeDeclaration": False},
                    "textDocument": {
                        "uri": pathlib.Path(os.path.join(self.repository_root_path, relative_file_path)).as_uri()
                    },
                    "position": {"line": line, "character": column},
                }
            )

        ret: List[multilspy_types.Location] = []
        assert isinstance(response, list), f"Unexpected response from Language Server: {response}"
        for item in response:
            assert isinstance(item, dict)
            assert LSPConstants.URI in item
            assert LSPConstants.RANGE in item

            new_item: multilspy_types.Location = {}
            new_item.update(item)
            new_item["absolutePath"] = PathUtils.uri_to_path(new_item["uri"])
            new_item["relativePath"] = PathUtils.get_relative_path(new_item["absolutePath"], self.repository_root_path)
            ret.append(multilspy_types.Location(**new_item))

        return ret

    async def request_completions(
        self, relative_file_path: str, line: int, column: int, allow_incomplete: bool = False
    ) -> List[multilspy_types.CompletionItem]:
        """
        Raise a [textDocument/completion](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_completion) request to the Language Server
        to find completions at the given line and column in the given file. Wait for the response and return the result.

        :param relative_file_path: The relative path of the file that has the symbol for which completions should be looked up
        :param line: The line number of the symbol
        :param column: The column number of the symbol

        :return List[multilspy_types.CompletionItem]: A list of completions
        """
        with self.open_file(relative_file_path):
            open_file_buffer = self.open_file_buffers[
                pathlib.Path(os.path.join(self.repository_root_path, relative_file_path)).as_uri()
            ]
            completion_params: LSPTypes.CompletionParams = {
                "position": {"line": line, "character": column},
                "textDocument": {"uri": open_file_buffer.uri},
                "context": {"triggerKind": LSPTypes.CompletionTriggerKind.Invoked},
            }
            response: Union[List[LSPTypes.CompletionItem], LSPTypes.CompletionList, None] = None

            num_retries = 0
            while response is None or (response["isIncomplete"] and num_retries < 30):
                await self.completions_available.wait()
                response: Union[
                    List[LSPTypes.CompletionItem], LSPTypes.CompletionList, None
                ] = await self.server.send.completion(completion_params)
                if isinstance(response, list):
                    response = {"items": response, "isIncomplete": False}
                num_retries += 1

            # TODO: Understand how to appropriately handle `isIncomplete`
            if response is None or (response["isIncomplete"] and not(allow_incomplete)):
                return []

            if "items" in response:
                response = response["items"]

            response: List[LSPTypes.CompletionItem] = response

            # TODO: Handle the case when the completion is a keyword
            items = [item for item in response if item["kind"] != LSPTypes.CompletionItemKind.Keyword]

            completions_list: List[multilspy_types.CompletionItem] = []

            for item in items:
                assert "insertText" in item or "textEdit" in item
                assert "kind" in item
                completion_item = {}
                if "detail" in item:
                    completion_item["detail"] = item["detail"]
                
                if "label" in item:
                    completion_item["completionText"] = item["label"]
                    completion_item["kind"] = item["kind"]
                elif "insertText" in item:
                    completion_item["completionText"] = item["insertText"]
                    completion_item["kind"] = item["kind"]
                elif "textEdit" in item and "newText" in item["textEdit"]:
                    completion_item["completionText"] = item["textEdit"]["newText"]
                    completion_item["kind"] = item["kind"]
                elif "textEdit" in item and "range" in item["textEdit"]:
                    new_dot_lineno, new_dot_colno = (
                        completion_params["position"]["line"],
                        completion_params["position"]["character"],
                    )
                    assert all(
                        (
                            item["textEdit"]["range"]["start"]["line"] == new_dot_lineno,
                            item["textEdit"]["range"]["start"]["character"] == new_dot_colno,
                            item["textEdit"]["range"]["start"]["line"] == item["textEdit"]["range"]["end"]["line"],
                            item["textEdit"]["range"]["start"]["character"]
                            == item["textEdit"]["range"]["end"]["character"],
                        )
                    )
                    
                    completion_item["completionText"] = item["textEdit"]["newText"]
                    completion_item["kind"] = item["kind"]
                elif "textEdit" in item and "insert" in item["textEdit"]:
                    assert False
                else:
                    assert False

                completion_item = multilspy_types.CompletionItem(**completion_item)
                completions_list.append(completion_item)

            return [
                json.loads(json_repr)
                for json_repr in set([json.dumps(item, sort_keys=True) for item in completions_list])
            ]

    async def request_document_symbols(self, relative_file_path: str) -> Tuple[List[multilspy_types.UnifiedSymbolInformation], Union[List[multilspy_types.TreeRepr], None]]:
        """
        Raise a [textDocument/documentSymbol](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_documentSymbol) request to the Language Server
        to find symbols in the given file. Wait for the response and return the result.

        :param relative_file_path: The relative path of the file that has the symbols

        :return Tuple[List[multilspy_types.UnifiedSymbolInformation], Union[List[multilspy_types.TreeRepr], None]]: A list of symbols in the file, and the tree representation of the symbols
        """
        with self.open_file(relative_file_path):
            response = await self.server.send.document_symbol(
                {
                    "textDocument": {
                        "uri": pathlib.Path(os.path.join(self.repository_root_path, relative_file_path)).as_uri()
                    }
                }
            )
        
        ret: List[multilspy_types.UnifiedSymbolInformation] = []
        l_tree = None
        assert isinstance(response, list), f"Unexpected response from Language Server: {response}"
        for item in response:
            assert isinstance(item, dict)
            assert LSPConstants.NAME in item
            assert LSPConstants.KIND in item

            if LSPConstants.CHILDREN in item:
                # TODO: l_tree should be a list of TreeRepr. Define the following function to return TreeRepr as well
                
                def visit_tree_nodes_and_build_tree_repr(tree: LSPTypes.DocumentSymbol) -> List[multilspy_types.UnifiedSymbolInformation]:
                    l: List[multilspy_types.UnifiedSymbolInformation] = []
                    children = tree['children'] if 'children' in tree else []
                    if 'children' in tree:
                        del tree['children']
                    l.append(multilspy_types.UnifiedSymbolInformation(**tree))
                    for child in children:
                        l.extend(visit_tree_nodes_and_build_tree_repr(child))
                    return l
                
                ret.extend(visit_tree_nodes_and_build_tree_repr(item))
            else:
                ret.append(multilspy_types.UnifiedSymbolInformation(**item))

        return ret, l_tree
    
    async def request_hover(self, relative_file_path: str, line: int, column: int) -> Union[multilspy_types.Hover, None]:
        """
        Raise a [textDocument/hover](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_hover) request to the Language Server
        to find the hover information at the given line and column in the given file. Wait for the response and return the result.

        :param relative_file_path: The relative path of the file that has the hover information
        :param line: The line number of the symbol
        :param column: The column number of the symbol

        :return None
        """
        with self.open_file(relative_file_path):
            response = await self.server.send.hover(
                {
                    "textDocument": {
                        "uri": pathlib.Path(os.path.join(self.repository_root_path, relative_file_path)).as_uri()
                    },
                    "position": {
                        "line": line,
                        "character": column,
                    },
                }
            )
        
        if response is None:
            return None

        assert isinstance(response, dict)

        return multilspy_types.Hover(**response)

    async def request_workspace_symbol(self, query: str) -> Union[List[multilspy_types.UnifiedSymbolInformation], None]:
        """
        Raise a [workspace/symbol](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#workspace_symbol) request to the Language Server
        to find symbols across the whole workspace. Wait for the response and return the result.

        :param query: The query string to filter symbols by

        :return Union[List[multilspy_types.UnifiedSymbolInformation], None]: A list of matching symbols
        """
        response = await self.server.send.workspace_symbol({"query": query})
        if response is None:
            return None

        assert isinstance(response, list)

        ret: List[multilspy_types.UnifiedSymbolInformation] = []
        for item in response:
            assert isinstance(item, dict)

            assert LSPConstants.NAME in item
            assert LSPConstants.KIND in item
            assert LSPConstants.LOCATION in item

            ret.append(multilspy_types.UnifiedSymbolInformation(**item))

        return ret


@ensure_all_methods_implemented(LanguageServer)
class SyncLanguageServer:
    """
    The SyncLanguageServer class provides a language agnostic interface to the Language Server Protocol.
    It is used to communicate with Language Servers of different programming languages.
    """

    def __init__(self, language_server: LanguageServer, timeout: Optional[int] = None):
        self.language_server = language_server
        self.loop = None
        self.loop_thread = None
        self.timeout = timeout

        # self._diagnostics: Dict[str, List[LSPTypes.Diagnostic]] = {}

    def _handle_diagnostics(self, params: Dict):
        """
        代理方法，将诊断处理委托给内部的 LanguageServer 实例。
        """
        self.language_server._handle_diagnostics(params)

    def request_diagnostics(self, relative_file_path: str) -> List[LSPTypes.Diagnostic]:
        """
        获取指定文件的诊断信息（错误、警告等）。
        
        :param relative_file_path: 要获取诊断信息的文件的相对路径
        
        :return List[LSPTypes.Diagnostic]: 文件的诊断项列表
        """
        result = asyncio.run_coroutine_threadsafe(
            self.language_server.request_diagnostics(relative_file_path), self.loop
        ).result(timeout=self.timeout)
        return result

    def request_code_actions(
        self, 
        relative_file_path: str, 
        range: multilspy_types.Range,
        diagnostics: Optional[List[LSPTypes.Diagnostic]] = None
    ) -> List[LSPTypes.CodeAction]:
        """
        向语言服务器发起代码操作请求，以查找文件中给定范围内可用的代码操作。
        
        :param relative_file_path: 要获取代码操作的文件的相对路径
        :param range: 文档中要获取代码操作的范围
        :param diagnostics: 可选的诊断列表，用于获取针对特定诊断的代码操作
        
        :return List[LSPTypes.CodeAction]: 可用代码操作的列表
        """
        result = asyncio.run_coroutine_threadsafe(
            self.language_server.request_code_actions(relative_file_path, range, diagnostics), self.loop
        ).result(timeout=self.timeout)
        return result
    
    def resolve_code_action(
        self,
        code_action: LSPTypes.CodeAction
    ) -> LSPTypes.CodeAction:
        """
        向语言服务器发起 [codeAction/resolve](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#codeAction_resolve) 请求，
        以解析代码操作的额外信息，如文档编辑。
        
        :param code_action: 要解析的代码操作对象
        
        :return LSPTypes.CodeAction: 解析后的代码操作对象
        """
        result = asyncio.run_coroutine_threadsafe(
            self.language_server.resolve_code_action(code_action), self.loop
        ).result(timeout=self.timeout)
        return result

    def apply_code_action(
        self,
        code_action: LSPTypes.CodeAction
    ) -> bool:
        """
        应用给定的代码操作，执行其编辑或命令。
        
        代码操作可以包含工作区编辑（更改文件内容）或命令（由语言服务器执行）。
        本方法会根据代码操作的类型执行相应操作。
        
        :param code_action: 要应用的代码操作
        
        :return bool: 操作是否成功应用
        """
        result = asyncio.run_coroutine_threadsafe(
            self.language_server.apply_code_action(code_action), self.loop
        ).result(timeout=self.timeout)
        return result
    
    def _apply_workspace_edit(
        self,
        workspace_edit: LSPTypes.WorkspaceEdit
    ) -> bool:
        """
        应用工作区编辑到相应的文件。
        
        :param workspace_edit: LSP规范的WorkspaceEdit对象
        
        :return bool: 编辑是否成功应用
        """
        result = asyncio.run_coroutine_threadsafe(
            self.language_server._apply_workspace_edit(workspace_edit), self.loop
        ).result(timeout=self.timeout)
        return result


    def _execute_command(
        self,
        command: LSPTypes.Command
    ) -> bool:
        """
        执行代码操作中的命令。
        
        :param command: LSP规范的Command对象
        
        :return bool: 命令是否成功执行
        """
        result = asyncio.run_coroutine_threadsafe(
            self.language_server._execute_command(command), self.loop
        ).result(timeout=self.timeout)
        return result

    @classmethod
    def create(
        cls, config: MultilspyConfig, logger: MultilspyLogger, repository_root_path: str, timeout: Optional[int] = None
    ) -> "SyncLanguageServer":
        """
        Creates a language specific LanguageServer instance based on the given configuration, and appropriate settings for the programming language.

        If language is Java, then ensure that jdk-17.0.6 or higher is installed, `java` is in PATH, and JAVA_HOME is set to the installation directory.

        :param repository_root_path: The root path of the repository (must be absolute).
        :param config: The Multilspy configuration.
        :param logger: The logger to use.

        :return SyncLanguageServer: A language specific LanguageServer instance.
        """
        return SyncLanguageServer(LanguageServer.create(config, logger, repository_root_path), timeout=timeout)

    def save_file(self, relative_file_path: str) -> None:
        """
        Notify the Language Server that a file has been saved.
        This does NOT actually write the buffer contents to disk, but only
        sends a notification to the Language Server that the file was saved.

        :param relative_file_path: The relative path of the file to mark as saved.
        :raises MultilspyException: If the Language Server is not started or the file is not open.
        """
        self.language_server.save_file(relative_file_path)

    @contextmanager
    def open_file(self, relative_file_path: str) -> Iterator[None]:
        """
        Open a file in the Language Server. This is required before making any requests to the Language Server.

        :param relative_file_path: The relative path of the file to open.
        """
        with self.language_server.open_file(relative_file_path):
            yield

    def insert_text_at_position(
        self, relative_file_path: str, line: int, column: int, text_to_be_inserted: str
    ) -> multilspy_types.Position:
        """
        Insert text at the given line and column in the given file and return 
        the updated cursor position after inserting the text.

        :param relative_file_path: The relative path of the file to open.
        :param line: The line number at which text should be inserted.
        :param column: The column number at which text should be inserted.
        :param text_to_be_inserted: The text to insert.
        """
        return self.language_server.insert_text_at_position(relative_file_path, line, column, text_to_be_inserted)

    def delete_text_between_positions(
        self,
        relative_file_path: str,
        start: multilspy_types.Position,
        end: multilspy_types.Position,
    ) -> str:
        """
        Delete text between the given start and end positions in the given file and return the deleted text.
        """
        return self.language_server.delete_text_between_positions(relative_file_path, start, end)

    def get_open_file_text(self, relative_file_path: str) -> str:
        """
        Get the contents of the given opened file as per the Language Server.

        :param relative_file_path: The relative path of the file to open.
        """
        return self.language_server.get_open_file_text(relative_file_path)
   
    @contextmanager
    def start_server(self) -> Iterator["SyncLanguageServer"]:
        """
        Starts the language server process and connects to it.

        :return: None
        """
        self.loop = asyncio.new_event_loop()
        loop_thread = threading.Thread(target=self.loop.run_forever, daemon=True)
        loop_thread.start()
        ctx = self.language_server.start_server()
        asyncio.run_coroutine_threadsafe(ctx.__aenter__(), loop=self.loop).result()
        yield self
        asyncio.run_coroutine_threadsafe(ctx.__aexit__(None, None, None), loop=self.loop).result()
        self.loop.call_soon_threadsafe(self.loop.stop)
        loop_thread.join()

    def request_definition(self, file_path: str, line: int, column: int) -> List[multilspy_types.Location]:
        """
        Raise a [textDocument/definition](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_definition) request to the Language Server
        for the symbol at the given line and column in the given file. Wait for the response and return the result.

        :param relative_file_path: The relative path of the file that has the symbol for which definition should be looked up
        :param line: The line number of the symbol
        :param column: The column number of the symbol

        :return List[multilspy_types.Location]: A list of locations where the symbol is defined
        """
        result = asyncio.run_coroutine_threadsafe(
            self.language_server.request_definition(file_path, line, column), self.loop
        ).result(timeout=self.timeout)
        return result

    def request_references(self, file_path: str, line: int, column: int) -> List[multilspy_types.Location]:
        """
        Raise a [textDocument/references](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_references) request to the Language Server
        to find references to the symbol at the given line and column in the given file. Wait for the response and return the result.

        :param relative_file_path: The relative path of the file that has the symbol for which references should be looked up
        :param line: The line number of the symbol
        :param column: The column number of the symbol

        :return List[multilspy_types.Location]: A list of locations where the symbol is referenced
        """
        result = asyncio.run_coroutine_threadsafe(
            self.language_server.request_references(file_path, line, column), self.loop
        ).result(timeout=self.timeout)
        return result

    def request_completions(
        self, relative_file_path: str, line: int, column: int, allow_incomplete: bool = False
    ) -> List[multilspy_types.CompletionItem]:
        """
        Raise a [textDocument/completion](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_completion) request to the Language Server
        to find completions at the given line and column in the given file. Wait for the response and return the result.

        :param relative_file_path: The relative path of the file that has the symbol for which completions should be looked up
        :param line: The line number of the symbol
        :param column: The column number of the symbol

        :return List[multilspy_types.CompletionItem]: A list of completions
        """
        result = asyncio.run_coroutine_threadsafe(
            self.language_server.request_completions(relative_file_path, line, column, allow_incomplete),
            self.loop,
        ).result(timeout=self.timeout)
        return result

    def request_document_symbols(self, relative_file_path: str) -> Tuple[List[multilspy_types.UnifiedSymbolInformation], Union[List[multilspy_types.TreeRepr], None]]:
        """
        Raise a [textDocument/documentSymbol](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_documentSymbol) request to the Language Server
        to find symbols in the given file. Wait for the response and return the result.

        :param relative_file_path: The relative path of the file that has the symbols

        :return Tuple[List[multilspy_types.UnifiedSymbolInformation], Union[List[multilspy_types.TreeRepr], None]]: A list of symbols in the file, and the tree representation of the symbols
        """
        result = asyncio.run_coroutine_threadsafe(
            self.language_server.request_document_symbols(relative_file_path), self.loop
        ).result(timeout=self.timeout)
        return result

    def request_hover(self, relative_file_path: str, line: int, column: int) -> Union[multilspy_types.Hover, None]:
        """
        Raise a [textDocument/hover](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_hover) request to the Language Server
        to find the hover information at the given line and column in the given file. Wait for the response and return the result.

        :param relative_file_path: The relative path of the file that has the hover information
        :param line: The line number of the symbol
        :param column: The column number of the symbol

        :return None
        """
        result = asyncio.run_coroutine_threadsafe(
            self.language_server.request_hover(relative_file_path, line, column), self.loop
        ).result(timeout=self.timeout)
        return result

    def request_workspace_symbol(self, query: str) -> Union[List[multilspy_types.UnifiedSymbolInformation], None]:
        """
        Raise a [workspace/symbol](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#workspace_symbol) request to the Language Server
        to find symbols across the whole workspace. Wait for the response and return the result.

        :param query: The query string to filter symbols by

        :return Union[List[multilspy_types.UnifiedSymbolInformation], None]: A list of matching symbols
        """
        result = asyncio.run_coroutine_threadsafe(
            self.language_server.request_workspace_symbol(query), self.loop
        ).result(timeout=self.timeout)
        return result
