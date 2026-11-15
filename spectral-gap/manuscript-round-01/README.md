# Centered permutation products

Problem 21 is selected for this conversation. The manuscript proves the requested matching-product estimate, explains its role in the biregular spectral argument, and develops exact mixed extrema and uniform diagonal asymptotics.

## Reading copies and scope

- [Mathematical manuscript](output/pdf/centered-permutation-products.pdf).
- [Eight-page illustrated guide](output/pdf/reading-guide.pdf).
- [Exact answer to problem 21 and submission readiness](../extension-round-02/SUBMISSION_READINESS.md).
- [Current contribution statement](../CONTRIBUTION.md) and [priority assessment](../extension-round-02/PRIORITY_SYNTHESIS.md).
- [Authoritative claim ledger](../CLAIM_LEDGER.md) and [active coordinator board](../extension-round-02/TEAM_BOARD.md).

The mixed theorem handles arbitrary powers and independent permutation colors. It identifies attained maxima when zero, one or two centered singletons conflict with the requested support. The scalar consequence implies Bordenave's Proposition 28. Section 8 identifies the half-edge permutation and explains the non-backtracking spectral proof chain.

For diagonal products, the original leading term is accurate exactly when k^3/N tends to zero. The later results give the parity transition, a sharp hierarchy of correction ranges, an explicit finite square-root error bound, and two optimal uniform rates for two specified approximations. The shorter quartic formula has an N^(-1/4) error on bounded square-root ranges. The full exact-denominator formula covers every 2<=k<=N and has worst error C_* N^(-1/3)+o(N^(-1/3)), with C_* approximately 0.39549627.

Classical overlap is substantial. The recurrence and leading terms, elementary factorial estimate, permanent bounds, Laguerre and derangement identities, and applicable Whittaker asymptotics are credited. No firstness certificate or new graph spectral theorem is claimed. Bordenave's full journal version has been checked, including the exact scope of the conditioning correction.

## Evidence and preservation

The [extension index](../extension-round-02/README.md) links the written proofs and separate reviews. The [verification record](VERIFICATION.md) distinguishes proof review, finite corroboration, source inspection and document integrity. The [handoff](HANDOFF.md) records continuation boundaries.

Earlier frozen inputs, manuscript revisions, reviews and manifests remain unchanged. A correction receives a later revision or separate addendum. The [final revision-10 manifest](frozen-manuscript-v10/MANIFEST.json) identifies the 41-page manuscript and eight-page guide exactly. The [final assembled review](../extension-round-02/reviews/assembled-v10-review.md) accepts these exact reading copies. Accepted scope is recorded in the ledger, not inferred merely from the existence of a PDF.

## Rebuild and portable checks

Requirements are Python 3 with matplotlib, numpy, mpmath, sympy and Pillow, a standard pdflatex installation with the packages in the source preambles, and Poppler for text and page comparisons. No network is required for the build or checks.

From this directory:

```bash
python3 build_artifacts.py
```

The script rebuilds four figures and their data, compiles both documents three times and rejects unresolved references or overflowing text. It writes the two PDFs under output/pdf. Mathematical check programs are separate.

Run `python3 checks/verify_package.py` on the supplied package before rebuilding to verify byte identity against frozen manifests. Rebuilding can change PDF timestamps. The portable replay instead checks content identity:

```bash
python3 checks/verify_release.py output/centered-permutation-final-package.zip
```

It extracts a fresh copy, verifies every archive entry and selected local links, replays the recorded finite checks, rebuilds both documents, and compares all text and page pixels against the final freeze. It also compares all plot data and images. Its receipt is saved outside the tested archive at `checks/release-verification.json`.

The [release assembler](package_release.py) includes the build and check dependencies, a portable index and the frozen evidence. Third-party paper downloads, full paper extracts, scratch renders, the separate historical import and other projects are excluded. The earlier accepted revision-5 release is retained separately in the workspace history.

No submission, publication or external correspondence has been performed. Author information and destination requirements remain for the user's final submission decision.
