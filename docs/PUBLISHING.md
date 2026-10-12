# GitHub publication status

Target: **[uplift-universal-inc/qzeta3-irrationality](https://github.com/uplift-universal-inc/qzeta3-irrationality)**.

As checked on 12 October 2026 (UTC), the user-created remote exists and is public. The GitHub connection authenticates as `fikreab-s`, has repository write permission, and lists the app installation under the owning personal account `uplift-universal-inc`.

The original prepared local commit is `d71a10fdc128c6763c228ef292af336e078ab14b`. That initial snapshot contained the manuscript, finite mathematical certificates, and an incomplete Lean skeleton. The formal-completion update adds checked proofs and build/axiom records and updates the manuscript's formal-status paragraphs. Historical source and review records are preserved.

**Published publicly with the owner's explicit approval.** The owner approved publication on 11 October 2026 (America/New_York). The connected GitHub app uploads the prepared file snapshot through GitHub's API because command-line Git has no login in this environment. Remote commit identifiers therefore differ from the original local preparation history, which is preserved in the previously supplied repository archive.

The initial publication contained the README, 16-page manuscript and LaTeX source, verification scripts and finite certificates, internal review and attribution records, the future-results inventory, and the nine-gap Lean skeleton.

The current formal-completion update replaces those production proof gaps and passes `make formal-proof`. The main theorem and explicit-series solution are among the audited declarations whose dependencies contain only `propext`, `Classical.choice`, and `Quot.sound`. The checked sufficient growth constant is `107/192`, with margin `31/576`; the sharper π-based manuscript estimate is not asserted as a formalized asymptotic. [VERIFICATION.md](VERIFICATION.md) identifies the records and the separate comparator-template exception. Publication of a snapshot and successful kernel verification are recorded as distinct events.

The elementary second-proof update adds the Gaussian residue identity, an alternate coefficient-content derivation, and direct irrationality assembly. Its cost `9/16` and margin `7/144` reproduce the sufficient bound in the retrieved source messages; the existing formal sieve already gives the stronger `107/192` cost. Appendix B documents this shared-construction variant, and `Meta/SecondProofAudit.lean` checks the use of its alternate arithmetic branch. The retrieved excerpts are preserved in `provenance/elementary-second-proof-source.md`; their linked scratch Markdown attachments were unavailable. No determinant-free proof or formalization of the excerpts' unrelated direct candidates is claimed.

The completed formal proof is supplied on the review branch
`lean/complete-reciprocal-qzeta3`. The default branch retains the initial
publication until the pull request is reviewed and merged.

To obtain the formal-completion snapshot:

```sh
git clone --branch lean/complete-reciprocal-qzeta3 https://github.com/uplift-universal-inc/qzeta3-irrationality.git
```

The manuscript/code outside the imported Lean package have no newly assigned open-source license. No external journal submission is part of this task.
