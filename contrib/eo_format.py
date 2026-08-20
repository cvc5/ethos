#!/usr/bin/env python3
"""Format Eunoia (.eo) files.

The formatter is intentionally small and syntax-directed.  It parses Eunoia as
S-expressions, keeps comments as nodes, uses 2-space indentation, and gives
program bodies special treatment so one-line cases align their returns.
"""

from __future__ import annotations

import argparse
import difflib
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Optional, Union


@dataclass(frozen=True)
class Token:
    kind: str
    text: str
    line: int
    col: int
    trailing: bool = False


@dataclass
class Node:
    kind: str
    text: str = ""
    children: Optional[list["Node"]] = None
    line: int = 0
    col: int = 0
    trailing: bool = False

    def is_atom(self, text: Optional[str] = None) -> bool:
        return self.kind == "atom" and (text is None or self.text == text)

    def is_comment(self) -> bool:
        return self.kind == "comment"

    def is_list(self) -> bool:
        return self.kind == "list"


class FormatError(Exception):
    pass


class Lexer:
    def __init__(self, text: str, name: str) -> None:
        self.text = text
        self.name = name
        self.pos = 0
        self.line = 1
        self.col = 0
        self.line_has_token = False

    def tokenize(self) -> list[Token]:
        tokens: list[Token] = []
        while not self._eof():
            ch = self._peek()
            if ch in " \t\r\n":
                self._advance()
                continue
            line, col = self.line, self.col
            if ch == ";":
                tokens.append(
                    Token(
                        "comment",
                        self._read_comment(),
                        line,
                        col,
                        self.line_has_token,
                    )
                )
            elif ch == "(":
                self._advance()
                tokens.append(Token("lparen", "(", line, col))
                self.line_has_token = True
            elif ch == ")":
                self._advance()
                tokens.append(Token("rparen", ")", line, col))
                self.line_has_token = True
            elif ch == '"':
                tokens.append(Token("atom", self._read_string(), line, col))
                self.line_has_token = True
            elif ch == "|":
                tokens.append(Token("atom", self._read_quoted_symbol(), line, col))
                self.line_has_token = True
            else:
                tokens.append(Token("atom", self._read_atom(), line, col))
                self.line_has_token = True
        return tokens

    def _eof(self) -> bool:
        return self.pos >= len(self.text)

    def _peek(self) -> str:
        return self.text[self.pos]

    def _advance(self) -> str:
        ch = self.text[self.pos]
        self.pos += 1
        if ch == "\n":
            self.line += 1
            self.col = 0
            self.line_has_token = False
        else:
            self.col += 1
        return ch

    def _read_comment(self) -> str:
        chars: list[str] = []
        while not self._eof() and self._peek() != "\n":
            chars.append(self._advance())
        return "".join(chars).rstrip()

    def _read_string(self) -> str:
        chars = [self._advance()]
        while not self._eof():
            ch = self._advance()
            chars.append(ch)
            if ch == '"':
                if not self._eof() and self._peek() == '"':
                    chars.append(self._advance())
                    continue
                return "".join(chars)
        raise FormatError(f"{self.name}:{self.line}:{self.col}: unterminated string")

    def _read_quoted_symbol(self) -> str:
        chars = [self._advance()]
        while not self._eof():
            ch = self._advance()
            chars.append(ch)
            if ch == "|":
                return "".join(chars)
        raise FormatError(
            f"{self.name}:{self.line}:{self.col}: unterminated quoted symbol"
        )

    def _read_atom(self) -> str:
        chars: list[str] = []
        while not self._eof():
            ch = self._peek()
            if ch in " \t\r\n();":
                break
            chars.append(self._advance())
        if not chars:
            raise FormatError(f"{self.name}:{self.line}:{self.col}: unexpected token")
        return "".join(chars)


class Parser:
    def __init__(self, tokens: list[Token], name: str) -> None:
        self.tokens = tokens
        self.name = name
        self.pos = 0

    def parse(self) -> list[Node]:
        nodes = self._parse_until_rparen(top_level=True)
        if self.pos != len(self.tokens):
            tok = self.tokens[self.pos]
            raise FormatError(f"{self.name}:{tok.line}:{tok.col}: trailing token")
        return nodes

    def _parse_until_rparen(self, top_level: bool) -> list[Node]:
        nodes: list[Node] = []
        while self.pos < len(self.tokens):
            tok = self.tokens[self.pos]
            if tok.kind == "rparen":
                if top_level:
                    raise FormatError(
                        f"{self.name}:{tok.line}:{tok.col}: unmatched ')'"
                    )
                break
            nodes.append(self._parse_one())
        return nodes

    def _parse_one(self) -> Node:
        tok = self.tokens[self.pos]
        self.pos += 1
        if tok.kind == "atom":
            return Node("atom", tok.text, None, tok.line, tok.col, tok.trailing)
        if tok.kind == "comment":
            return Node("comment", tok.text, None, tok.line, tok.col, tok.trailing)
        if tok.kind != "lparen":
            raise FormatError(f"{self.name}:{tok.line}:{tok.col}: unexpected ')'")
        children = self._parse_until_rparen(top_level=False)
        if self.pos >= len(self.tokens):
            raise FormatError(f"{self.name}:{tok.line}:{tok.col}: unmatched '('")
        self.pos += 1
        return Node("list", "", children, tok.line, tok.col, tok.trailing)


class Formatter:
    def __init__(self, width: int, indent_style: str, indent_size: int) -> None:
        self.width = width
        self.indent_style = indent_style
        self.indent_size = indent_size

    def format_document(self, nodes: list[Node]) -> str:
        lines: list[str] = []
        idx = 0
        while idx < len(nodes):
            node = nodes[idx]
            if node.is_comment():
                self.emit_comment(lines, node, 0)
                idx += 1
            else:
                command_start = len(lines)
                lines.extend(self.format_node(node, 0))
                idx += 1
                while (
                    idx < len(nodes)
                    and nodes[idx].is_comment()
                    and nodes[idx].trailing
                ):
                    self.emit_comment(lines, nodes[idx], 0, command_start)
                    idx += 1
                if idx < len(nodes):
                    self.ensure_blank_line(lines)
        while lines and lines[-1] == "":
            lines.pop()
        return "\n".join(lines) + "\n"

    def ensure_blank_line(self, lines: list[str]) -> None:
        if lines and lines[-1] != "":
            lines.append("")

    def format_node(self, node: Node, level: int) -> list[str]:
        if node.is_atom():
            return [self.indent(level) + node.text]
        if node.is_comment():
            return self.format_comment(node, level)
        if self._is_program(node):
            return self.format_program(node, level)
        return self.format_list(node, level)

    def format_comment(self, node: Node, level: int) -> list[str]:
        return self.format_comment_with_indent(node, self.indent(level))

    def format_comment_with_indent(self, node: Node, indent: str) -> list[str]:
        text = node.text
        if self.line_width(indent + text) <= self.width:
            return [indent + text]

        semis = len(text) - len(text.lstrip(";"))
        if semis == 0:
            return [indent + text]
        prefix = text[:semis]
        body = text[semis:]
        if body.startswith(" "):
            prefix += " "
            body = body[1:]
        if " " not in body.strip():
            return [indent + text]

        available = self.width - self.line_width(indent + prefix)
        if available < 20:
            return [indent + text]

        lines: list[str] = []
        current = prefix
        for word in body.split():
            maybe = current + ("" if current == prefix else " ") + word
            if self.line_width(indent + maybe) > self.width and current != prefix:
                lines.append(indent + current.rstrip())
                current = prefix + word
            else:
                current = maybe
        lines.append(indent + current.rstrip())
        return lines

    def emit_comment(
        self,
        lines: list[str],
        node: Node,
        level: int,
        insert_before: Optional[int] = None,
    ) -> None:
        if node.trailing and lines and not lines[-1].lstrip().startswith(";"):
            trailing = " " + node.text
            if self.line_width(lines[-1] + trailing) <= self.width:
                lines[-1] += trailing
                return
            target = insert_before if insert_before is not None else len(lines) - 1
            # Skip past comments already moved to this location so repeated
            # inserts keep their original relative order instead of reversing.
            while target < len(lines) and lines[target].lstrip().startswith(";"):
                target += 1
            indent_ref = target if target < len(lines) else len(lines) - 1
            lines[target:target] = self.format_comment_with_indent(
                node, self.leading_whitespace(lines[indent_ref])
            )
            return
        lines.extend(self.format_comment(node, level))

    def leading_whitespace(self, text: str) -> str:
        return text[: len(text) - len(text.lstrip(" \t"))]

    def format_program(self, node: Node, level: int) -> list[str]:
        flat = self.flat(node)
        if flat is not None and self.line_width(self.indent(level) + flat) <= self.width:
            return [self.indent(level) + flat]

        children = node.children or []
        parts = self.non_comment_children(node)
        if len(parts) < 6:
            return self.format_list(node, level)

        command, name, params, sig_keyword, arg_types, ret_type = parts[:6]
        body = parts[6] if len(parts) > 6 else None
        if not command.is_atom("program") or not sig_keyword.is_atom(":signature"):
            return self.format_list(node, level)

        lines: list[str] = []
        positions = {id(child): idx for idx, child in enumerate(children)}

        def emit_comments_between(start: int, end: int, insert_before: int) -> None:
            for child in children[start:end]:
                if child.is_comment():
                    self.emit_comment(lines, child, level + 1, insert_before)

        head = self.indent(level) + f"(program {name.text}"
        params_flat = self.flat(params)
        pre_param_comments = [
            child
            for child in children[positions[id(name)] + 1 : positions[id(params)]]
            if child.is_comment()
        ]
        if pre_param_comments:
            lines.append(head)
            for child in pre_param_comments:
                self.emit_comment(lines, child, level + 1)
            params_start = len(lines)
            lines.extend(self.format_node(params, level + 1))
        else:
            if (
                params_flat is not None
                and self.line_width(head + " " + params_flat) <= self.width
            ):
                params_start = len(lines)
                lines.append(head + " " + params_flat)
            else:
                lines.append(head)
                params_start = len(lines)
                lines.extend(self.format_node(params, level + 1))

        emit_comments_between(
            positions[id(params)] + 1, positions[id(sig_keyword)], params_start
        )

        sig = self.indent(level + 1) + ":signature"
        args_flat = self.flat(arg_types)
        ret_flat = self.flat(ret_type)
        sig_start = len(lines)
        if (
            args_flat is not None
            and ret_flat is not None
            and self.line_width(f"{sig} {args_flat} {ret_flat}") <= self.width
        ):
            lines.append(f"{sig} {args_flat} {ret_flat}")
        else:
            lines.append(sig)
            lines.extend(self.format_node(arg_types, level + 2))
            lines.extend(self.format_node(ret_type, level + 2))

        body_pos = positions[id(body)] if body is not None else len(children)
        emit_comments_between(positions[id(ret_type)] + 1, body_pos, sig_start)

        if body is not None:
            body_start = len(lines)
            if body.is_list():
                lines.extend(self.format_program_body(body, level + 1))
            else:
                lines.extend(self.format_node(body, level + 1))
            emit_comments_between(body_pos + 1, len(children), body_start)

        lines.append(self.indent(level) + ")")
        return lines

    def format_program_body(self, body: Node, level: int) -> list[str]:
        children = body.children or []
        if not children:
            return [self.indent(level) + "()"]

        case_level = level
        case_info = self.program_case_info(children, case_level)
        inline_cols = self.inline_program_cases(children, case_info)

        lines = [self.indent(level) + "("]
        last_child_start = 0
        for idx, child in enumerate(children):
            if child.is_comment():
                self.emit_comment(lines, child, case_level, last_child_start)
            elif idx in inline_cols:
                info = case_info[idx]
                assert info is not None
                last_child_start = len(lines)
                lines.append(
                    self.format_inline_case(
                        info["pattern"], info["ret"], inline_cols[idx], case_level
                    )
                )
            elif self.is_program_case(child):
                last_child_start = len(lines)
                lines.extend(self.format_multiline_case(child, case_level))
            else:
                last_child_start = len(lines)
                lines.extend(self.format_node(child, case_level))
        lines.append(self.indent(level) + ")")
        return lines

    def is_program_case(self, node: Node) -> bool:
        return node.is_list() and len(self.non_comment_children(node)) == 2

    def program_case_info(
        self, children: list[Node], case_level: int
    ) -> dict[int, Optional[dict[str, Union[int, str]]]]:
        info: dict[int, Optional[dict[str, Union[int, str]]]] = {}
        for idx, child in enumerate(children):
            if not child.is_list():
                info[idx] = None
                continue
            parts = self.non_comment_children(child)
            if len(parts) != 2:
                info[idx] = None
                continue
            pattern = self.flat(parts[0])
            ret = self.flat(parts[1])
            if pattern is None or ret is None:
                info[idx] = None
                continue
            before_ret = self.indent_col(case_level) + 1 + self.line_width(pattern)
            info[idx] = {
                "pattern": pattern,
                "ret": ret,
                "min_ret_col": self.next_even(before_ret + 1),
                "ret_width": self.line_width(ret),
            }
        return info

    def inline_program_cases(
        self,
        children: list[Node],
        case_info: dict[int, Optional[dict[str, Union[int, str]]]],
    ) -> dict[int, int]:
        inline_cols: dict[int, int] = {}
        group: list[int] = []
        trailing_comments = self.trailing_program_case_comments(children, case_info)

        def base_case_fits(idx: int, return_col: int) -> bool:
            info = case_info[idx]
            assert info is not None
            return return_col + int(info["ret_width"]) + 1 <= self.width

        def trailing_comment_fits(idx: int, return_col: int) -> bool:
            info = case_info[idx]
            assert info is not None
            return (
                return_col
                + int(info["ret_width"])
                + 2
                + self.line_width(trailing_comments[idx].text)
                <= self.width
            )

        moved_comment_cases = {
            idx
            for idx in trailing_comments
            if base_case_fits(idx, int(case_info[idx]["min_ret_col"]))
            and not trailing_comment_fits(idx, int(case_info[idx]["min_ret_col"]))
        }
        moved_comment_indices = {idx + 1 for idx in moved_comment_cases}

        def case_fits(idx: int, return_col: int) -> bool:
            if not base_case_fits(idx, return_col):
                return False
            if idx in trailing_comments and idx not in moved_comment_cases:
                return trailing_comment_fits(idx, return_col)
            return True

        def flush_group() -> None:
            if not group:
                return
            return_col = max(int(case_info[idx]["min_ret_col"]) for idx in group)
            for idx in group:
                inline_cols[idx] = return_col
            group.clear()

        for idx, child in enumerate(children):
            if idx in moved_comment_cases:
                flush_group()
            info = case_info.get(idx)
            if child.is_comment():
                if idx in moved_comment_indices:
                    continue
                flush_group()
                continue
            if info is None:
                flush_group()
                continue
            own_col = int(info["min_ret_col"])
            if not case_fits(idx, own_col):
                flush_group()
                continue
            trial = group + [idx]
            return_col = max(int(case_info[i]["min_ret_col"]) for i in trial)
            if all(case_fits(i, return_col) for i in trial):
                group.append(idx)
            else:
                flush_group()
                group.append(idx)
        flush_group()
        return inline_cols

    def trailing_program_case_comments(
        self,
        children: list[Node],
        case_info: dict[int, Optional[dict[str, Union[int, str]]]],
    ) -> dict[int, Node]:
        trailing_comments: dict[int, Node] = {}
        for idx, child in enumerate(children[:-1]):
            if case_info.get(idx) is None:
                continue
            next_child = children[idx + 1]
            if next_child.is_comment() and next_child.trailing:
                trailing_comments[idx] = next_child
        return trailing_comments

    def format_inline_case(
        self, pattern: str, ret: str, return_col: int, case_level: int
    ) -> str:
        prefix = self.indent(case_level) + "(" + pattern
        spaces = max(1, return_col - self.line_width(prefix))
        return prefix + (" " * spaces) + ret + ")"

    def format_multiline_case(self, case: Node, case_level: int) -> list[str]:
        parts = self.non_comment_children(case)
        if len(parts) != 2:
            return self.format_list(case, case_level)
        pattern, ret = parts
        lines = self.format_node_with_prefix(
            pattern, self.indent(case_level) + "(", case_level + 1
        )
        ret_lines = self.format_node(ret, case_level + 1)
        lines.extend(ret_lines)
        self.append_suffix(lines, ")", case_level)
        return lines

    def format_list(self, node: Node, level: int) -> list[str]:
        children = node.children or []
        flat = self.flat(node)
        if (
            not self.force_multiline(node)
            and flat is not None
            and self.line_width(self.indent(level) + flat) <= self.width
        ):
            return [self.indent(level) + flat]

        if (
            level == 0
            and children
            and children[0].is_atom()
            and not self.keeps_first_child_on_head_line(children)
        ):
            return self.format_top_level_command(children, level)

        if self.keeps_first_child_on_head_line(children):
            return self.format_head_with_first_child(children, level)

        if self.should_wrap_flat_children(node, level):
            return self.format_wrapped_flat_children(children, level)

        if children and children[0].is_atom():
            first = children[0].text
            lines = [self.indent(level) + "(" + first]
            last_child_start = 0
            for child in children[1:]:
                if child.is_comment():
                    self.emit_comment(lines, child, level + 1, last_child_start)
                else:
                    last_child_start = len(lines)
                    lines.extend(self.format_node(child, level + 1))
            if level == 0 or lines[-1].lstrip().startswith(";"):
                lines.append(self.indent(level) + ")")
            else:
                self.append_suffix(lines, ")", level)
            return lines

        lines = [self.indent(level) + "("]
        last_child_start = 0
        for child in children:
            if child.is_comment():
                self.emit_comment(lines, child, level + 1, last_child_start)
            else:
                last_child_start = len(lines)
                lines.extend(self.format_node(child, level + 1))
        if level == 0 or lines[-1].lstrip().startswith(";"):
            lines.append(self.indent(level) + ")")
        else:
            self.append_suffix(lines, ")", level)
        return lines

    def keeps_first_child_on_head_line(self, children: list[Node]) -> bool:
        if len(children) < 2 or not children[0].is_atom():
            return False
        return children[0].text in {"eo::define", "eo::ite"}

    def force_multiline(self, node: Node) -> bool:
        return (
            self.is_call(node, "eo::define")
            and len(self.non_comment_children(node)) > 2
        )

    def format_head_with_first_child(
        self, children: list[Node], level: int
    ) -> list[str]:
        head = children[0].text
        child_level = level + 1
        prefix = self.indent(level) + "(" + head + " "
        lines = self.format_node_with_prefix(children[1], prefix, child_level)
        last_child_start = 0
        for child in children[2:]:
            next_level = self.head_child_level(head, child, level)
            if child.is_comment():
                self.emit_comment(lines, child, next_level, last_child_start)
            else:
                last_child_start = len(lines)
                lines.extend(self.format_node(child, next_level))
        if lines[-1].lstrip().startswith(";"):
            lines.append(self.indent(level) + ")")
        else:
            self.append_suffix(lines, ")", level)
        return lines

    def head_child_level(self, head: str, child: Node, level: int) -> int:
        if head == "eo::define" and self.is_call(child, "eo::define"):
            return level
        return level + 1

    def is_call(self, node: Node, head: str) -> bool:
        children = self.non_comment_children(node) if node.is_list() else []
        return bool(children and children[0].is_atom(head))

    def format_node_with_prefix(
        self, node: Node, prefix: str, child_level: int
    ) -> list[str]:
        if node.is_atom():
            return [prefix + node.text]
        if node.is_comment():
            lines = [prefix.rstrip()]
            self.emit_comment(lines, node, child_level)
            return lines

        flat = self.flat(node)
        if flat is not None and self.line_width(prefix + flat) <= self.width:
            return [prefix + flat]

        children = node.children or []
        if not children:
            return [prefix + "()"]

        lines = self.format_node_with_prefix(
            children[0], prefix + "(", child_level + 1
        )
        last_child_start = 0
        for child in children[1:]:
            if child.is_comment():
                self.emit_comment(lines, child, child_level + 1, last_child_start)
            else:
                last_child_start = len(lines)
                lines.extend(self.format_node(child, child_level + 1))
        self.append_suffix(lines, ")", child_level)
        return lines

    def format_top_level_command(self, children: list[Node], level: int) -> list[str]:
        lines: list[str] = []
        line = self.indent(level) + "(" + children[0].text
        idx = 1

        while idx < len(children):
            child = children[idx]
            if child.is_comment() or self.is_keyword(child):
                break
            child_flat = self.flat(child)
            if child_flat is None:
                break
            maybe = line + " " + child_flat
            if self.line_width(maybe) > self.width:
                break
            line = maybe
            idx += 1

        lines.append(line)
        last_child_start = 0
        while idx < len(children):
            child = children[idx]
            if child.is_comment():
                self.emit_comment(lines, child, level + 1, last_child_start)
                idx += 1
                continue
            if self.is_keyword(child):
                last_child_start = len(lines)
                idx = self.format_keyword_group(children, idx, lines, level)
                continue
            last_child_start = len(lines)
            lines.extend(self.format_node(child, level + 1))
            idx += 1
        self.close_top_level_command(lines, children[0].text, level)
        return lines

    def close_top_level_command(
        self, lines: list[str], command: str, level: int
    ) -> None:
        if command == "declare-rule" or not lines:
            lines.append(self.indent(level) + ")")
        else:
            self.append_suffix(lines, ")", level)

    def format_keyword_group(
        self, children: list[Node], idx: int, lines: list[str], level: int
    ) -> int:
        if children[idx].is_atom(":requires"):
            return self.format_requires_keyword_group(children, idx, lines, level)

        line = self.indent(level + 1) + children[idx].text
        idx += 1
        while idx < len(children):
            child = children[idx]
            if child.is_comment() or self.is_keyword(child):
                break
            child_flat = self.flat(child)
            if child_flat is None:
                break
            maybe = line + " " + child_flat
            if self.line_width(maybe) > self.width:
                break
            line = maybe
            idx += 1
        lines.append(line)
        while idx < len(children):
            child = children[idx]
            if child.is_comment() or self.is_keyword(child):
                break
            lines.extend(self.format_node(child, level + 2))
            idx += 1
        return idx

    def format_requires_keyword_group(
        self, children: list[Node], idx: int, lines: list[str], level: int
    ) -> int:
        line = self.indent(level + 1) + children[idx].text
        idx += 1
        if idx >= len(children):
            lines.append(line)
            return idx

        child = children[idx]
        if child.is_comment() or self.is_keyword(child):
            lines.append(line)
            return idx

        child_flat = self.flat(child)
        if child_flat is not None:
            maybe = line + " " + child_flat
            if self.line_width(maybe) <= self.width:
                lines.append(maybe)
                return idx + 1

        lines.append(line)
        if child.is_list():
            lines.extend(self.format_requires_list(child, level + 2))
        else:
            lines.extend(self.format_node(child, level + 2))
        return idx + 1

    def format_requires_list(self, node: Node, level: int) -> list[str]:
        flat = self.flat(node)
        if (
            flat is not None
            and self.line_width(self.indent(level) + flat) <= self.width
        ):
            return [self.indent(level) + flat]

        children = node.children or []
        if not children:
            return [self.indent(level) + "()"]

        lines: list[str] = []
        opened = False
        last_child_start = 0
        for child in children:
            if child.is_comment():
                if not opened:
                    lines.append(self.indent(level) + "(")
                    opened = True
                self.emit_comment(lines, child, level + 1, last_child_start)
                continue
            if not opened:
                last_child_start = len(lines)
                lines.extend(
                    self.format_node_with_prefix(
                        child, self.indent(level) + "(", level + 1
                    )
                )
                opened = True
            else:
                last_child_start = len(lines)
                lines.extend(
                    self.format_node_with_prefix(
                        child, self.indent(level + 1), level + 2
                    )
                )
        self.append_suffix(lines, ")", level)
        return lines

    def format_wrapped_flat_children(self, children: list[Node], level: int) -> list[str]:
        if not children:
            return [self.indent(level) + "()"]

        lines: list[str] = []
        current = self.indent(level) + "("
        for child in children:
            child_flat = self.flat(child)
            assert child_flat is not None
            sep = "" if current.endswith("(") else " "
            maybe = current + sep + child_flat
            if not current.endswith("(") and self.line_width(maybe + ")") > self.width:
                lines.append(current)
                current = self.indent(level + 1) + child_flat
            else:
                current = maybe
        if self.line_width(current + ")") <= self.width:
            lines.append(current + ")")
        else:
            lines.append(current)
            lines.append(self.indent(level) + ")")
        return lines

    def should_wrap_flat_children(self, node: Node, level: int) -> bool:
        children = node.children or []
        if not children:
            return False
        for child in children:
            child_flat = self.flat(child)
            if child_flat is None:
                return False
            if (
                not child.is_atom()
                and self.line_width(self.indent(level + 1) + child_flat)
                > self.width
            ):
                return False
        if level == 0 and children[0].is_atom():
            return False
        return True

    def append_suffix(self, lines: list[str], suffix: str, level: int) -> None:
        comment_idx = self.trailing_comment_index(lines[-1]) if lines else None
        if comment_idx is not None:
            before = lines[-1][:comment_idx].rstrip()
            if not before.strip():
                lines.append(self.indent(level) + suffix)
                return
            comment = lines[-1][comment_idx:]
            maybe = before + suffix + " " + comment
            if self.line_width(maybe) <= self.width:
                lines[-1] = maybe
            else:
                lines.append(self.indent(level) + suffix)
            return
        if lines and self.line_width(lines[-1] + suffix) <= self.width:
            lines[-1] += suffix
        else:
            lines.append(self.indent(level) + suffix)

    def trailing_comment_index(self, text: str) -> Optional[int]:
        in_string = False
        in_symbol = False
        i = 0
        while i < len(text):
            ch = text[i]
            if in_string:
                if ch == '"':
                    if i + 1 < len(text) and text[i + 1] == '"':
                        i += 2
                        continue
                    in_string = False
            elif in_symbol:
                if ch == "|":
                    in_symbol = False
            elif ch == '"':
                in_string = True
            elif ch == "|":
                in_symbol = True
            elif ch == ";":
                return i
            i += 1
        return None

    def flat(self, node: Node) -> Optional[str]:
        if node.is_atom():
            return node.text
        if node.is_comment():
            return None
        pieces: list[str] = []
        for child in node.children or []:
            child_flat = self.flat(child)
            if child_flat is None:
                return None
            pieces.append(child_flat)
        return "(" + " ".join(pieces) + ")"

    def non_comment_children(self, node: Node) -> list[Node]:
        return [child for child in node.children or [] if not child.is_comment()]

    def _is_program(self, node: Node) -> bool:
        children = self.non_comment_children(node)
        return bool(children and children[0].is_atom("program"))

    def is_keyword(self, node: Node) -> bool:
        return node.is_atom() and node.text.startswith(":")

    def indent(self, level: int) -> str:
        if self.indent_style == "tabs":
            return "\t" * level
        return " " * (self.indent_size * level)

    def indent_col(self, level: int) -> int:
        return self.indent_size * level

    def line_width(self, text: str) -> int:
        col = 0
        for ch in text:
            if ch == "\t":
                step = self.indent_size - (col % self.indent_size)
                col += step
            else:
                col += 1
        return col

    @staticmethod
    def next_even(value: int) -> int:
        return value if value % 2 == 0 else value + 1


def parse_eunoia(text: str, name: str) -> list[Node]:
    return Parser(Lexer(text, name).tokenize(), name).parse()


def decode_eunoia_string(text: str) -> Optional[str]:
    if len(text) < 2 or not (text.startswith('"') and text.endswith('"')):
        return None
    result: list[str] = []
    i = 1
    while i < len(text) - 1:
        ch = text[i]
        if ch == '"' and i + 1 < len(text) - 1 and text[i + 1] == '"':
            result.append('"')
            i += 2
        else:
            result.append(ch)
            i += 1
    return "".join(result)


def iter_include_paths(nodes: Iterable[Node]) -> Iterable[str]:
    for node in nodes:
        if not node.is_list():
            continue
        children = [child for child in node.children or [] if not child.is_comment()]
        if len(children) < 2:
            continue
        if not children[0].is_atom("include"):
            continue
        if not children[1].is_atom():
            continue
        path = decode_eunoia_string(children[1].text)
        if path is not None:
            yield path


def should_format_include(path: Path) -> bool:
    return path.suffix == ".eo" or path.suffix == ""


def collect_files(paths: list[Path], recursive: bool) -> list[Path]:
    ordered: list[Path] = []
    seen: set[Path] = set()

    def visit(path: Path) -> None:
        resolved = path.resolve()
        if resolved in seen:
            return
        seen.add(resolved)
        if not resolved.exists():
            raise FormatError(f"{path}: file does not exist")
        text = resolved.read_text(encoding="utf-8")
        nodes = parse_eunoia(text, str(resolved))
        if recursive:
            for include in iter_include_paths(nodes):
                include_path = Path(include)
                if not include_path.is_absolute():
                    include_path = resolved.parent / include_path
                if include_path.exists() and should_format_include(include_path):
                    visit(include_path)
                elif not include_path.exists():
                    print(
                        f"warning: {resolved}: include does not exist: {include}",
                        file=sys.stderr,
                    )
        ordered.append(resolved)

    for path in paths:
        visit(path)
    return ordered


def format_file(path: Path, formatter: Formatter) -> tuple[str, str]:
    original = path.read_text(encoding="utf-8")
    formatted = formatter.format_document(parse_eunoia(original, str(path)))
    return original, formatted


def unified_diff(path: Path, original: str, formatted: str) -> str:
    return "".join(
        difflib.unified_diff(
            original.splitlines(keepends=True),
            formatted.splitlines(keepends=True),
            fromfile=str(path),
            tofile=str(path),
        )
    )


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="+", type=Path)
    parser.add_argument("--width", type=int, default=80)
    parser.add_argument(
        "--indent-size",
        type=int,
        default=2,
        help="number of spaces per indentation level",
    )
    parser.add_argument(
        "--no-recursive",
        action="store_false",
        dest="recursive",
        help="format only the requested files, not files reached by include",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="do not write files; exit nonzero if formatting would change",
    )
    parser.add_argument(
        "--diff",
        action="store_true",
        help="print a unified diff instead of writing files",
    )
    args = parser.parse_args(argv)

    formatter = Formatter(args.width, "spaces", args.indent_size)
    try:
        files = collect_files(args.files, args.recursive)
        changed: list[Path] = []
        for path in files:
            original, formatted = format_file(path, formatter)
            if original == formatted:
                continue
            changed.append(path)
            if args.diff:
                print(unified_diff(path, original, formatted), end="")
            elif not args.check:
                path.write_text(formatted, encoding="utf-8")
        if args.check and changed:
            for path in changed:
                print(f"would reformat {path}", file=sys.stderr)
        elif not args.diff and not args.check:
            for path in changed:
                print(f"reformatted {path}")
        return 1 if (args.check and changed) else 0
    except FormatError as err:
        print(f"eofmt: {err}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
