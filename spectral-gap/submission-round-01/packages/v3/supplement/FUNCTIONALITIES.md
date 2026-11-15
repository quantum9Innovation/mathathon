# Portable finite-check evidence

This supplement preserves three original review checkers, their saved results and review texts. It includes the exact proof packet dependencies read by the two-conflict checker. SOURCE_PROVENANCE.json records the original workspace locations and SHA-256 identities.

The replay.py entry point copies the evidence to a fresh temporary directory, runs each checker with a 300-second wall limit, a 300-second CPU limit and a 2 GiB address-space limit, and compares every result field and report byte with the saved result. It verifies the preserved copied inputs before and after execution and saves a separate receipt. No checker source adaptation is used.
