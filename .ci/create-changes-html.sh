#!/bin/sh
if [ $# != 2 ]; then
    echo >&2 "usage: $0 BASE_DOC_COMMIT DOC_REPO"
    echo >&2 "creates CHANGES.html in the current directory"
    echo >&2 "for the diffs of DOC_REPO against BASE_DOC_COMMIT"
    exit 1
fi
BASE_DOC_COMMIT="$1"
DOC_REPOSITORY="$2"

# Wipe out chronic diffs between old doc and new doc
(cd $DOC_REPOSITORY && find . -name "*.html" | xargs sed -i -e '\;<script type="application/vnd\.jupyter\.widget-state+json">;,\;</script>; d')
# Create CHANGES.html
echo '<html>' > CHANGES.html
echo '<head>' >> CHANGES.html
echo '<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/styles/default.min.css">' >> CHANGES.html
echo '<script src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/highlight.min.js"></script>' >> CHANGES.html
echo '<script>hljs.highlightAll();</script>' >> CHANGES.html
cat >> CHANGES.html << EOF
<script>
document.addEventListener('DOMContentLoaded', () => {
const diffSite = 'https://pianomister.github.io/diffsite'
const baseDocURL = 'https://sagemath-tobias.netlify.app'
const diffParagraphs = document.querySelectorAll('p.diff');
diffParagraphs.forEach(paragraph => {
  const rootURL = window.location.origin;
  const docAnchor = paragraph.querySelector('a');  // first "a" element
  const url = new URL(docAnchor.href);
  const path = url.pathname;
  const anchor = document.createElement('a');
  anchor.href = diffSite + '/?url1=' + rootURL + path + '&url2=' + baseDocURL + path;
  anchor.textContent = 'compare with the base';
  anchor.setAttribute('target', '_blank');
  paragraph.appendChild(anchor);
  paragraph.innerHTML += '&nbsp;';
  const hunkAnchors = paragraph.querySelectorAll('a.hunk');
  hunkAnchors.forEach(hunkAnchor => {
    const url = new URL(hunkAnchor.href);
    const path = url.pathname;
    const pathHash = path + url.hash.replace('#', '%23');
    const anchor = document.createElement('a');
    anchor.href = diffSite + '/?url1=' + rootURL + pathHash + '&url2=' + baseDocURL + path;
    anchor.textContent = hunkAnchor.textContent;
    anchor.setAttribute('target', '_blank');
    paragraph.appendChild(anchor);
    paragraph.innerHTML += '&nbsp;';
  });
});
});
</script>
EOF
echo '</head>' >> CHANGES.html
echo '<body>' >> CHANGES.html
(cd $DOC_REPOSITORY && git diff $BASE_DOC_COMMIT -- *.html) > diff.txt
python3 - << EOF
import os, re, html
with open('diff.txt', 'r') as f:
    diff_text = f.read()
diff_blocks = re.split(r'^(?=diff --git)', diff_text, flags=re.MULTILINE)
out_blocks = []
for block in diff_blocks:
    match = re.search(r'^diff --git a/(.*) b/\1', block, flags=re.MULTILINE)
    if match:
        doc = match.group(1)
        file_path = os.path.join('$DOC_REPOSITORY', doc)
        try:
            with open(file_path, 'r') as file:
                content = file.readlines()
        except FileNotFoundError:
            content = []
        count = 0
        for line in block.splitlines():
            if line.startswith('@@ -'):
                search_result = re.search(r'@@ -(\d+),(\d+) \+(\d+),(\d+)', line)
                if search_result:
                    line_number = int(search_result.group(3))
                    for i in range(line_number - 1, -1, -1):
                        if content[i].startswith('<'):
                            count += 1
                            content[i] = f'<span id="hunk{count}" style="visibility: hidden;"></span>' + content[i]
                            break
        if content:
            with open(file_path, 'w') as file:
                file.writelines(content)
        path = 'html/' + doc
        hunks = '&nbsp;'.join(f'<a href="{path}#hunk{i+1}" class="hunk" target="_blank">#{i + 1}</a>' for i in range(count))
        out_blocks.append(f'<p class="diff"><a href="{path}">{doc}</a>&nbsp;' + hunks + '&emsp;</p>'
                            + '\n<pre><code class="language-diff">'
                            + html.escape(block).strip() + '</code></pre>')
output_text = '\n'.join(out_blocks)
with open('diff.html', 'w') as f:
    f.write(output_text)
EOF
cat diff.html >> CHANGES.html
echo '</body>' >> CHANGES.html
echo '</html>' >> CHANGES.html
rm diff.txt diff.html
