"""Turn a pytest JUnit report into GitHub annotations, one per failing test.

A failed step otherwise surfaces only "Process completed with exit code 1";
the test names and messages live in the job log. Annotations are readable
through the API and on the run page.

    python tools/ci_annotate.py junit.xml
"""
import sys
import xml.etree.ElementTree as ET


def main(path):
    try:
        root = ET.parse(path).getroot()
    except (OSError, ET.ParseError) as exc:
        print(f"::warning title=ci_annotate::no JUnit report at {path}: {exc}")
        return 0
    n = 0
    for case in root.iter("testcase"):
        for kind in ("failure", "error"):
            el = case.find(kind)
            if el is None:
                continue
            n += 1
            name = f"{case.get('classname', '')}::{case.get('name', '')}"
            msg = (el.get("message") or el.text or "").strip().replace("\r", "")
            msg = msg.replace("%", "%25").replace("\n", "%0A")[:3000]
            print(f"::error title={kind.upper()} {name}::{msg}")
    print(f"{n} failing test(s) annotated")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
