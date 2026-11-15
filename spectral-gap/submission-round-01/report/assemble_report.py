"""Assemble one self-contained report from the preserved mathematical source."""
from pathlib import Path
from hashlib import sha256
import json
import math
import re

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT.parent / 'manuscript-round-01' / 'frozen-manuscript-v10'


def coordinates(points):
    return ' '.join(f'({x:.12g},{y:.12g})' for x, y in points)


def curve(points, style, legend=None):
    result = '\\addplot[' + style + '] coordinates {' + coordinates(points) + '};\n'
    if legend:
        result += '\\addlegendentry{' + legend + '}\n'
    return result


def axis(content, xlabel, ylabel, title, limits, width='.46\\textwidth', height='5.6cm'):
    options = ['width=' + width, 'height=' + height, 'xlabel={' + xlabel + '}',
               'ylabel={' + ylabel + '}', 'title={' + title + '}', limits,
               'axis lines=left', 'grid=major', 'grid style={gray!15}',
               'tick label style={font=\\scriptsize}', 'label style={font=\\scriptsize}',
               'title style={font=\\small}', 'legend style={font=\\tiny,draw=none,fill=none}',
               'legend pos=north west', 'unbounded coords=jump']
    return '\\begin{tikzpicture}\n\\begin{axis}[' + ','.join(options) + ']\n' + content + '\\end{axis}\n\\end{tikzpicture}'


def inline_figures():
    figures = BASE / 'figures'
    moment = json.loads((figures / 'moment-regimes-data.json').read_text())
    rate = json.loads((figures / 'rate-and-hierarchy-data.json').read_text())
    glob = json.loads((figures / 'global-error-data.json').read_text())
    blue, orange = 'draw=proofblue,thick', 'draw=prooforange,thick'
    vals = [9 * i / 199 for i in range(200)]
    left = curve([(x, math.cosh(2 * math.sqrt(x) / 3)) for x in vals], blue, 'Even limit')
    left += curve([(x, math.sinh(2 * math.sqrt(x) / 3) / (2 * math.sqrt(x) / 3) if x else 1) for x in vals], orange, 'Odd limit')
    for parity, color, mark in [(0, 'proofblue', 'o'), (1, 'prooforange', 'square')]:
        points = [(v['c'], v['ratio']) for v in moment['critical'] if v['k'] % 2 == parity]
        left += curve(points, f'only marks,mark={mark},mark size=1.1pt,draw={color}')
    right = curve([(2 * i / 199, math.exp((2 * i / 199) ** 2 / 4)) for i in range(200)], 'black,thick', '$e^{t^2/4}$')
    for n, style, label in [(10000, orange + ',dashed', '$N=10^4$'), (1000000, blue + ',dotted', '$N=10^6$')]:
        right += curve([(v['t'], v['ratio_to_H']) for v in moment['boundary'] if v['N'] == n], style, label)
    out = {'moment-regimes': axis(left, '$k^3/N$', '$R_k$', 'Parity transition', 'xmin=0,xmax=9') + '\\hfill\n' + axis(right, '$t=k/\\sqrt N$', '$R_k/H_k$', 'Next correction', 'xmin=0,xmax=2,ymin=.94,ymax=2.85')}
    xs = [2 * i / 249 for i in range(250)]
    left = ''
    for parity, style, label in [(0, blue, 'Even limit'), (1, orange, 'Odd limit')]:
        left += curve([(x, (2 * parity - 1) * math.sqrt(x) / 2 + 2 * x ** 2.5 / 15) for x in xs], style, label)
    for n, mark in [(10000, 'o'), (1000000, 'square')]:
        for parity, color in [(0, 'proofblue'), (1, 'prooforange')]:
            left += curve([(v['scale'], v['scaled_error']) for v in rate['signed_error'] if v['N'] == n and v['k'] % 2 == parity], f'only marks,mark={mark},mark size=1.1pt,draw={color}')
    right = curve([(x, 2 * x ** 2.5 / 15) for x in xs], 'black,thick', '$2c^{5/2}/15$')
    for n, style, label in [(10000, orange + ',dashed', '$N=10^4$'), (1000000, blue + ',dotted', '$N=10^6$')]:
        right += curve([(v['scale'], v['log_ratio_after_quartic']) for v in rate['hierarchy'] if v['N'] == n], style, label)
    out['rate-and-hierarchy'] = axis(left, '$c=k/\\sqrt N$', '$N^{1/4}(W_{N,k}-1)$', 'Signed first error', 'xmin=0,xmax=2') + '\\hfill\n' + axis(right, '$c=k/N^{3/5}$', '$\\log W_{N,k}$', 'First omitted exponent', 'xmin=0,xmax=2')
    xs = [0] + [.002 + (5 - .002) * i / 449 for i in range(450)]
    plot = ''
    for parity, style, label in [(0, blue, 'Even limit'), (1, orange, 'Odd limit')]:
        points = []
        for x in xs:
            ell = 2 * x ** 1.5 / 3
            y = 0 if x == 0 else 3 / (4 * x) * (2 * ell / (math.exp(2 * ell) + 1)) if parity == 0 else -3 / (4 * x) * (1 - 2 * ell / math.expm1(2 * ell))
            points.append((x, y))
        plot += curve(points, style, label)
    for n, mark in [(1000, 'o'), (1000000, 'square')]:
        for parity, color in [(0, 'proofblue'), (1, 'prooforange')]:
            plot += curve([(v['scale'], v['scaled_error']) for v in glob['critical_profile_samples'] if v['N'] == n and v['k'] % 2 == parity], f'only marks,mark={mark},mark size=1.2pt,draw={color}')
    out['global-error'] = axis(plot, '$c=k/N^{1/3}$', 'Scaled relative error', 'Full-range approximation', 'xmin=0,xmax=5', width='.88\\textwidth', height='6cm')
    return out


def tex_escape(value):
    table = {'&': r'\&', '%': r'\%', '$': r'\$', '#': r'\#', '_': r'\_', '{': r'\{', '}': r'\}'}
    return ''.join(table.get(c, c) for c in value)


def main():
    manifest = json.loads((BASE / 'MANIFEST.json').read_text())
    for item in manifest:
        assert sha256((BASE / item['path']).read_bytes()).hexdigest() == item['sha256']
    source = (BASE / 'manuscript/main.tex').read_text()
    source = source.replace(r'\usepackage{graphicx,booktabs,array,xcolor}', r'\usepackage{graphicx,booktabs,array,xcolor,pgfplots}' + '\n' + r'\pgfplotsset{compat=1.18}' + '\n' + r'\definecolor{proofblue}{HTML}{176B8A}' + '\n' + r'\definecolor{prooforange}{HTML}{BB5B28}')
    source = source.replace(r'\hypersetup{pdftitle={Centered permutation products},pdfsubject={Sharp mixed envelopes and uniform diagonal asymptotics}}', r'\hypersetup{pdftitle={Gaps in spectral-gap literature},pdfsubject={Problem 21: a row-sum proof and its spectral role}}')
    source = source.replace(r'\title{Centered permutation products:\\ sharp envelopes and uniform asymptotics}', r'\title{Gaps in spectral-gap literature:\\ a row-sum proof and its spectral role}')
    metadata = json.loads((ROOT / 'metadata/team.json').read_text())
    author_lines = []
    if metadata['team_name']:
        author_lines.append(tex_escape(metadata['team_name']))
    if metadata['authors'] and all(not person.get('affiliation') for person in metadata['authors']):
        author_lines.append(r'\quad '.join(tex_escape(person['name']) for person in metadata['authors']))
    else:
        for person in metadata['authors']:
            author_lines.append(tex_escape(person['name']) + (r'\quad ' + tex_escape(person['affiliation']) if person.get('affiliation') else ''))
    source = source.replace(r'\author{}', '\\author{' + r'\\'.join(author_lines) + '}')
    source = source.replace(r'\date{November 14, 2026}', r'\date{Problem 21\quad Track: Combinatorics\\November 15, 2026}')
    abstract = r'''\begin{abstract}
We give an intuitive proof of the centered permutation-product estimate used in Bordenave's Proposition 28 and the biregular spectral-gap argument of Brito, Dumitriu and Harris. Compatible conditioning leaves a smaller uniform permutation matrix whose exact row sum yields a positive recurrence. Keeping this cancellation before expanding the other factors handles arbitrary powers and independent permutation colors. The resulting envelope is attained for zero, one or two conflicting centered singletons. We explain the non-backtracking norm-moment argument and its algebraic bridge to adjacency, while keeping the graph path and tangle estimates as cited inputs. Quantitative extensions determine the sharp cubic scale, parity transition and uniform errors of specified diagonal-moment approximations. Known recurrences, factorial inequalities and classical asymptotic methods are credited. The report proves the probabilistic input and explains its spectral role, without asserting a new graph eigenvalue theorem.
\end{abstract}'''
    source = re.sub(r'\\begin\{abstract\}.*?\\end\{abstract\}', lambda _: abstract, source, flags=re.S)
    record = (ROOT / 'report/submission-record.txt').read_text()
    source = source.replace(r'\begingroup\small', record + '\n' + r'\begingroup\small', 1)
    order = ['introduction', 'mixed', 'spectral', 'threshold', 'critical', 'extensions', 'asymptotics', 'rates', 'conditioning', 'discussion']
    start = source.index(r'\input{sections/introduction}')
    end = source.index(r'\appendix')
    source = source[:start] + '\n'.join(r'\input{sections/' + x + '}' for x in order) + '\n' + source[end:]
    preserved = []
    def expand(match):
        name = match.group(1)
        path = BASE / 'manuscript' / (name + '.tex')
        content = path.read_text()
        preserved.append({'path': str(path.relative_to(BASE)), 'sha256': sha256(content.encode()).hexdigest()})
        return '% Begin preserved mathematical section: ' + name + '\n' + content + '\n% End preserved mathematical section\n'
    source = re.sub(r'\\input\{([^}]+)\}', expand, source)
    figures = inline_figures()
    for name, content in figures.items():
        pattern = r'\\includegraphics\[[^]]+\]\{\.\./figures/' + re.escape(name) + r'\.pdf\}'
        source, count = re.subn(pattern, lambda _: content, source)
        assert count == 1, name
    assert not re.search(r'\\(?:input|include|includegraphics|bibliography)\b', source)
    source = source.replace(r'\begin{document}', r'\pdfinfoomitdate=1' + '\n' + r'\pdftrailerid{}' + '\n' + r'\pdfsuppressptexinfo=15' + '\n' + r'\begin{document}', 1)
    target = ROOT / 'report/report.tex'
    target.write_text(source)
    proof_environments = r'\\begin\{(theorem|proposition|lemma|corollary|proof|example)\}.*?\\end\{\1\}'
    original = '\n'.join((BASE / x['path']).read_text() for x in preserved)
    old_blocks = [m.group(0) for m in re.finditer(proof_environments, original, re.S)]
    new_blocks = [m.group(0) for m in re.finditer(proof_environments, source, re.S)]
    assert sorted(old_blocks) == sorted(new_blocks)
    receipt = {'baseline_manifest_sha256': sha256((BASE / 'MANIFEST.json').read_bytes()).hexdigest(),
               'report_sha256': sha256(target.read_bytes()).hexdigest(), 'section_sources': preserved,
               'preserved_math_blocks': len(old_blocks), 'math_blocks_identical': True,
               'inline_vector_figures': len(figures), 'external_report_assets': [],
               'team_metadata_status': metadata['status'],
               'changes': ['New title, abstract and submission record', 'Spectral section moved directly after mixed-product section', 'Section source expanded inline', 'Three plots embedded as vector coordinates from preserved data and analytic formulas', 'Deterministic PDF metadata settings']}
    (ROOT / 'checks/ASSEMBLY.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'section_sources'}, indent=2))


if __name__ == '__main__':
    main()
