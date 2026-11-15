# Bordenave journal-version check

Checked November 14, 2026 Pacific against the publisher's complete article. This supersedes the journal-access limitation in the frozen first priority audit. It does not alter that historical audit.

## Source identity

Charles Bordenave, A new proof of Friedman's second eigenvalue theorem and its extension to random lifts, Annales scientifiques de l'Ecole normale superieure 53(6), 2020, pages 1393 to 1439. [DOI record](https://doi.org/10.24033/asens.2450), [publisher download](https://smf.emath.fr/download/pdf/1498332).

The PDF was retrieved from the public download linked by the publisher. No login, contact form, payment or correspondence was used. The [publisher access policy](https://smf.emath.fr/publications/abonnements-aux-revues-electroniques) makes older issues publicly accessible. The retrieved file has 50 PDF pages, including three pages preceding the article. Its SHA256 is `3525c6b35737292db97d165ca38bdead95a991cef27a8d7a1e39d86b27fa58bc`.

| Passage | Printed page | PDF page, counted from one | Result |
| --- | --- | --- | --- |
| Proposition 28 | 1426 | 36 | The mixed centered-product estimate is present |
| Proof and exposure setup | 1427 | 37 | The proof exposes images and preimages |
| Equation (62) | 1428 | 38 | The displayed sigma algebra, event, denominator and bound agree with the preprint assertion under review |
| Continuation of the estimate | 1429 | 39 | Later bounds depend on the conditional step |

Pages 36 and 38 were rendered and visually inspected in addition to text extraction. The journal page numbers are now the primary manuscript citations. The preprint numbering remains useful as a secondary reference.

## What fails and what survives

At n=4, cells (1,1) and (1,2) make the displayed conditioning reveal the tested indicator. On an atom where the first row maps to column one, its conditional expectation is one. The source event makes its displayed answer zero, and its proposed upper bound is one third.

For disjoint cells (1,1) and (2,2), condition on the second row mapping to column three and the preimage of column two being row four. Two arrows are exposed. The tested indicator has conditional expectation one half, while the displayed denominator gives one third. This is an atom of the stated conditioning, of probability one twelfth.

These are exact finite counterexamples to the intermediate assertion. They are not counterexamples to Proposition 28 or to the article's spectral theorem. The compatible-prescribed-match proof in manuscript Section 2 establishes the required mixed estimate without using that assertion. The existing exact-enumeration records and the separate source review support these examples.

## Priority and remaining limits

The publisher entry, author's publications page and targeted searches did not identify a linked erratum addressing this formula. That negative search does not prove that no correction or private observation exists. No first-discovery claim is made for the conditioning defect.

This check resolves whether the published formula differs from the cited preprint. It is not an end-to-end audit of the journal article, and no author or editor has been contacted.
