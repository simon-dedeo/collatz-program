"""consult_sol.py -- one focused question to gpt-5.6-sol. Never prints the key.
Usage: python3 consult_sol.py <promptfile> <outfile>
"""
import json, sys, urllib.request, ssl
try:
    import certifi
    _CTX = ssl.create_default_context(cafile=certifi.where())
except Exception:
    _CTX = ssl.create_default_context()

KEYPATH = '/Users/simon/Desktop/DANIEL/API_KEY'


def ask(prompt):
    key = open(KEYPATH).read().strip()
    body = json.dumps({
        "model": "gpt-5.6-sol",
        "input": prompt,
        "reasoning": {"effort": "high"},
    }).encode()
    req = urllib.request.Request(
        "https://api.openai.com/v1/responses", data=body,
        headers={"Authorization": "Bearer " + key,
                 "Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=600, context=_CTX) as r:
        data = json.load(r)
    # extract text
    out = []
    for item in data.get("output", []):
        for c in item.get("content", []):
            if c.get("type") in ("output_text", "text"):
                out.append(c.get("text", ""))
    return "\n".join(out), data.get("id", "")


if __name__ == '__main__':
    prompt = open(sys.argv[1]).read()
    txt, rid = ask(prompt)
    with open(sys.argv[2], 'w') as f:
        f.write(txt)
    with open(sys.argv[2] + '.id', 'w') as f:
        f.write(rid)
    print('wrote', sys.argv[2], 'id', rid, 'len', len(txt))
