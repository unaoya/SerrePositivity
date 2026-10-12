#!/usr/bin/env python3
"""Check active repository links and exposition API/module references after lake build.
Historical documents retain their old API names; only their local links are checked.
Lean's environment is exported to a temporary directory, never into the repository.
"""
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    failures = []
    docs = [ROOT / 'README.md', *sorted((ROOT / 'notes').rglob('*.md'))]
    for path in docs:
        for target in re.findall(r'(?<!\w)\[[^]\n]*\]\(([^)]+)\)', path.read_text()):
            target = target.strip('<>').split('#', 1)[0]
            if not target or re.match(r'[a-zA-Z]+://|app:', target):
                continue
            if not (path.parent / target).exists():
                failures.append(f'{path.relative_to(ROOT)}: missing link {target}')
    with tempfile.TemporaryDirectory(prefix='serre-doc-check-') as directory:
        directory = Path(directory)
        names_path = directory / 'names.txt'
        source = directory / 'Export.lean'
        source.write_text('import SerrePositivity\nimport Lean.Elab.Command\n'
            'open Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n'
            '  let mut names : Array String := #[]\n'
            '  for (n, _) in env.constants do\n    names := names.push n.toString\n'
            f'  liftIO <| IO.FS.writeFile "{names_path}" '
            '(String.intercalate "\\n" names.toList)\n')
        subprocess.run(['lake', 'env', 'lean', str(source)], cwd=ROOT, check=True)
        names = set(names_path.read_text().splitlines())
    modules = {str(p.relative_to(ROOT)).removesuffix('.lean').replace('/', '.')
               for p in (ROOT / 'SerrePositivity').rglob('*.lean')}
    directories = {str(p.relative_to(ROOT)).replace('/', '.')
                   for p in (ROOT / 'SerrePositivity').rglob('*') if p.is_dir()}
    labels = set(re.findall(r'\\ld\{([^}]+)\}',
                           (ROOT / 'exposition/ja/exposition-ja.tex').read_text()))
    candidates = names | modules | directories
    references = 0
    for label in sorted(labels):
        token = label.split()[0]
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', token):
            continue  # Mathematical expressions and literal repository paths.
        if token in {'adc7f124', 'SerrePositivity'}:
            continue  # Source provenance / namespace notation.
        references += 1
        if token in candidates or 'SerrePositivity.' + token in candidates:
            continue
        if any(n.endswith('.' + token) for n in candidates):
            continue  # Short names are resolved in the surrounding mathematical context.
        failures.append(f'exposition: unresolved API/module {label}')
    for failure in failures:
        print(failure)
    print(f'Checked {len(docs)} Markdown files and {references} exposition references; '
          f'{len(failures)} failures.')
    return bool(failures)


if __name__ == '__main__':
    raise SystemExit(main())
