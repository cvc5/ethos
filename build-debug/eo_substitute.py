import re
import os
import sys

def read_eunoia_file(path, seen=None):
    if seen is None:
        seen = set()

    abs_path = os.path.abspath(path)
    if abs_path in seen:
        return []

    print(f"📄 Including: {abs_path}")
    seen.add(abs_path)

    expressions = []
    with open(abs_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Handle includes recursively
    include_pattern = re.compile(r'\(include\s+"([^"]+)"\)')
    for match in include_pattern.finditer(content):
        include_path = os.path.join(os.path.dirname(abs_path), match.group(1))
        expressions += read_eunoia_file(include_path, seen)

    # Remove includes for parsing
    content = include_pattern.sub('', content)

    # Extract top-level s-expressions with balanced parentheses
    expressions_raw = []
    i = 0
    while i < len(content):
        if content[i] == '(':
            start = i
            depth = 1
            i += 1
            while i < len(content) and depth > 0:
                if content[i] == '(':
                    depth += 1
                elif content[i] == ')':
                    depth -= 1
                i += 1
            if depth == 0:
                expressions_raw.append(content[start:i].strip())
        else:
            i += 1

    return expressions + expressions_raw

def find_matching_expr(exprs, command_template):
    print(f"🔍 Looking for match for: $$EO_{command_template}$$")

    # Handle: declare-const X (matches both const and type variants)
    if command_template.startswith("declare-const "):
        name = re.escape(command_template[len("declare-const "):])
        patterns = [
            re.compile(r'^\(\s*declare-const\s+' + name + r'(\s|\))'),
            re.compile(r'^\(\s*declare-parameterized-const\s+' + name + r'(\s|\))'),
            re.compile(r'^\(\s*declare-type\s+' + name + r'(\s|\))'),
        ]
        for expr in exprs:
            if any(pat.match(expr) for pat in patterns):
                return expr
        return None

    # Handle: fwd-decl X
    if command_template.startswith("fwd-decl "):
        name = re.escape(command_template[len("fwd-decl "):])
        pat = re.compile(r'^\(\s*program\s+' + name + r'(\s|\)).*:signature', re.DOTALL)
        for expr in exprs:
            if pat.search(expr):
                return expr
        return None

    # General case
    head = re.escape(command_template.strip())
    pat = re.compile(r'^\(\s*' + head + r'(\s|\))')
    for expr in exprs:
        if pat.match(expr):
            return expr
    return None

def replace_templates(template_text, exprs):
    missing = []

    def repl(match):
        command_template = match.group(1)
        expr = find_matching_expr(exprs, command_template)
        if not expr:
            missing.append(command_template)
            return match.group(0)
        return expr

    # Updated pattern: allow any visible character except the second $$ (non-greedy up to $$)
    result = re.sub(r'\$\$EO_((?:[^$]|\$[^$])+)?\$\$', repl, template_text)

    if missing:
        print("\n❌ ERROR: The following commands could not be matched:")
        for cmd in missing:
            print(f"  - $$EO_{cmd}$$")
        #sys.exit(1)

    return result

if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("Usage: python3 eunoia_substitute.py <eunoia_file> <template_file> <output_file>")
        sys.exit(1)

    eunoia_file = sys.argv[1]
    template_file = sys.argv[2]
    output_file = sys.argv[3]

    seen_files = set()
    exprs = read_eunoia_file(eunoia_file, seen=seen_files)

    with open(template_file, 'r', encoding='utf-8') as tf:
        template_text = tf.read()

    substituted = replace_templates(template_text, exprs)

    with open(output_file, 'w', encoding='utf-8') as out:
        out.write(substituted)

    print(f"\n✅ Output written to: {output_file}")
