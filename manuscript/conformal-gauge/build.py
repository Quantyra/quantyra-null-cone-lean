"""Compile the separate paper and render all pages for human/agent inspection.

Usage: python manuscript/conformal-gauge/build.py --tectonic PATH
Requires PyMuPDF. This does not invoke Lean or declare visual review complete.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import pymupdf as fitz

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--tectonic',default='tectonic')
args=parser.parse_args()
folder=Path(__file__).resolve().parent
root=folder.parents[1]
source=folder/'conformal-gauge-counterexample.tex'
result=subprocess.run([args.tectonic,'--keep-logs','-o',str(folder),str(source)],cwd=root,capture_output=True)
(folder/'tex-build.log').write_bytes(result.stdout+result.stderr)
print((result.stdout+result.stderr).decode('utf-8',errors='replace'))
assert result.returncode==0, 'Tectonic compilation failed'
doc=fitz.open(source.with_suffix('.pdf'))
out=root/'tmp/conformal-gauge-review';out.mkdir(parents=True,exist_ok=True)
page_hashes={}
for i,page in enumerate(doc):
    path=out/f'page-{i+1:02}.png'
    page.get_pixmap(matrix=fitz.Matrix(1.5,1.5)).save(path)
    page_hashes[path.name]=hashlib.sha256(path.read_bytes()).hexdigest()
for group in range((len(doc)+1)//2):
    sheet=fitz.open();page=sheet.new_page(width=1300,height=900)
    for j in range(2):
        n=2*group+j
        if n>=len(doc):break
        x=j*650
        page.insert_text((x+12,17),f'Page {n+1}',fontsize=12)
        page.show_pdf_page(fitz.Rect(x+5,25,x+645,895),doc,n)
    page.get_pixmap().save(out/f'contact-{group+1}.png')
render={'pages':len(doc),'page_render_sha256':page_hashes,'visual_review_complete':False}
(out/'renders.json').write_text(json.dumps(render,indent=2)+'\n',encoding='utf-8',newline='\n')
print('Compiled',len(doc),'pages; inspect renders at',out)
