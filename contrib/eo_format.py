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
from typing import Iterable, Optional


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
    children: list["Node"] | None = None
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
        for node in nodes:
            if node.is_comment():
                self.emit_comment(lines, node, 0)
            else:
                lines.extend(self.format_node(node, 0))
        while lines and lines[-1] == "":
            lines.pop()
        return "\n".join(lines) + "\n"

    def format_node(self, node: Node, level: int) -> list[str]:
        if node.is_atom():
            return [self.indent(level) + node.text]
        if node.is_comment():
            return self.format_comment(node, level)
        if self._is_program(node):
            return self.format_program(node, level)
        return self.format_list(node, level)

    def format_comment(self, node: Node, level: int) -> list[str]:
        indent = self.indent(level)
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

    def emit_comment(self, lines: list[str], node: Node, level: int) -> None:
        if node.trailing and lines and not lines[-1].lstrip().startswith(";"):
            trailing = " " + node.text
            if self.line_width(lines[-1] + trailing) <= self.width:
                lines[-1] += trailing
                return
        lines.extend(self.format_comment(node, level))

    def format_program(self, node: Node, level: int) -> list[str]:
        flat = self.flat(node)
        if flat is not None and self.line_width(self.indent(level) + flat) <= self.width:
            return [self.indent(level) + flat]

        parts = self.non_comment_children(node)
        if len(parts) < 6:
            return self.format_list(node, level)

        command, name, params, sig_keyword, arg_types, ret_type = parts[:6]
        body = parts[6] if len(parts) > 6 else None
        if not command.is_atom("program") or not sig_keyword.is_atom(":signature"):
            return self.format_list(node, level)

        lines: list[str] = []
        head = self.indent(level) + f"(program {name.text}"
        params_flat = self.flat(params)
        if (
            params_flat is not None
            and self.line_width(head + " " + params_flat) <= self.width
        ):
            lines.append(head + " " + params_flat)
        else:
            lines.append(head)
            lines.extend(self.format_node(params, level + 1))

        sig = self.indent(level + 1) + ":signature"
        args_flat = self.flat(arg_types)
        ret_flat = self.flat(ret_type)
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

        for child in node.children or []:
            if child.is_comment():
                self.emit_comment(lines, child, level + 1)

        if body is not None:
            if body.is_list():
                lines.extend(self.format_program_body(body, level + 1))
            else:
                lines.extend(self.format_node(body, level + 1))

        lines.append(self.indent(level) + ")")
        return lines

    def format_program_body(self, body: Node, level: int) -> list[str]:
        children = body.children or []
        if not children:
            return [self.indent(level) + "()"]

        case_level = level
        case_info = self.program_case_info(children, case_level)
        inline_indexes, return_col = self.inline_program_cases(case_info)

        lines = [self.indent(level) + "("]
        for idx, child in enumerate(children):
            if child.is_comment():
                self.emit_comment(lines, child, case_level)
            elif idx in inline_indexes:
                info = case_info[idx]
                assert info is not None
                lines.append(
                    self.format_inline_case(
                        info["pattern"], info["ret"], return_col, case_level
                    )
                )
            elif case_info.get(idx) is not None:
                lines.extend(self.format_multiline_case(child, case_level))
            else:
                lines.extend(self.format_node(child, case_level))
        lines.append(self.indent(level) + ")")
        return lines

    def program_case_info(
        self, children: list[Node], case_level: int
    ) -> dict[int, Optional[dict[str, str]]]:
        info: dict[int, Optional[dict[str, str]]] = {}
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
                "min_ret_col": str(self.next_even(before_ret + 1)),
            }
        return info

    def inline_program_cases(
        self, case_info: dict[int, Optional[dict[str, str]]]
    ) -> tuple[set[int], int]:
        inline = {idx for idx, info in case_info.items() if info is not None}
        return_col = 0
        while inline:
            return_col = max(
                int(case_info[idx]["min_ret_col"])  # type: ignore[index]
                for idx in inline
            )
            new_inline = {
                idx
                for idx in inline
                if return_col
                + self.line_width(case_info[idx]["ret"])  # type: ignore[index]
                + 1
                <= self.width
            }
            if new_inline == inline:
                break
            inline = new_inline
        return inline, return_col

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
        pattern_flat = self.flat(pattern)
        lines: list[str] = []
        if (
            pattern_flat is not None
            and self.line_width(self.indent(case_level) + "(" + pattern_flat)
            <= self.width
        ):
            lines.append(self.indent(case_level) + "(" + pattern_flat)
        else:
            lines.append(self.indent(case_level) + "(")
            lines.extend(self.format_node(pattern, case_level + 1))
        ret_lines = self.format_node(ret, case_level + 1)
        lines.extend(ret_lines)
        self.append_suffix(lines, ")", case_level)
        return lines

    def format_list(self, node: Node, level: int) -> list[str]:
        flat = self.flat(node)
        if flat is not None and self.line_width(self.indent(level) + flat) <= self.width:
            return [self.indent(level) + flat]

        children = node.children or []
        if level == 0 and children and children[0].is_atom():
            return self.format_top_level_command(children, level)

        if self.keeps_first_child_on_head_line(children):
            return self.format_head_with_first_child(children, level)

        if self.should_wrap_flat_children(node, level):
            return self.format_wrapped_flat_children(children, level)

        if children and children[0].is_atom():
            first = children[0].text
            lines = [self.indent(level) + "(" + first]
            for child in children[1:]:
                if child.is_comment():
                    self.emit_comment(lines, child, level + 1)
                else:
                    lines.extend(self.format_node(child, level + 1))
            if level == 0 or lines[-1].lstrip().startswith(";"):
                lines.append(self.indent(level) + ")")
            else:
                self.append_suffix(lines, ")", level)
            return lines

        lines = [self.indent(level) + "("]
        for child in children:
            if child.is_comment():
                self.emit_comment(lines, child, level + 1)
            else:
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

    def format_head_with_first_child(
        self, children: list[Node], level: int
    ) -> list[str]:
        head = children[0].text
        prefix = self.indent(level) + "(" + head + " "
        lines = self.format_node_with_prefix(children[1], prefix, level + 1)
        for child in children[2:]:
            if child.is_comment():
                self.emit_comment(lines, child, level + 1)
            else:
                lines.extend(self.format_node(child, level + 1))
        if level == 0 or lines[-1].lstrip().startswith(";"):
            lines.append(self.indent(level) + ")")
        else:
            self.append_suffix(lines, ")", level)
        return lines

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
        for child in children[1:]:
            if child.is_comment():
                self.emit_comment(lines, child, child_level + 1)
            else:
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
        while idx < len(children):
            child = children[idx]
            if child.is_comment():
                self.emit_comment(lines, child, level + 1)
                idx += 1
                continue
            if self.is_keyword(child):
                idx = self.format_keyword_group(children, idx, lines, level)
                continue
            lines.extend(self.format_node(child, level + 1))
            idx += 1
        lines.append(self.indent(level) + ")")
        return lines

    def format_keyword_group(
        self, children: list[Node], idx: int, lines: list[str], level: int
    ) -> int:
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
        if lines and self.line_width(lines[-1] + suffix) <= self.width:
            lines[-1] += suffix
        else:
            lines.append(self.indent(level) + suffix)

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
        text = resolved.read_text()
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
    original = path.read_text()
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
                path.write_text(formatted)
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
