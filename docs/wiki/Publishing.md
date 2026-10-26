# Publishing the source-controlled pages to the GitHub Wiki

The authoritative page sources live at [`docs/wiki/`](https://github.com/shulda/lean_eppa_semigeneric/tree/main/docs/wiki) in the **public** Lean repository. They follow the source-controlled publishing pattern of [`lean_all_those_eppa_classes`](https://github.com/shulda/lean_all_those_eppa_classes/tree/main/docs/wiki), itself adapted from [Jan Hubička's Milliken project](https://github.com/janhubicka/lean-milliken/wiki).

The [publishing workflow](https://github.com/shulda/lean_eppa_semigeneric/blob/main/.github/workflows/publish-wiki.yml) is **separate from the Lean proof CI**. It runs after changes to `docs/wiki/**` or to its own workflow, on GitHub Wiki `gollum` events, or by manual dispatch.

## Initial Wiki setup (only if required)

GitHub's **Wiki feature may be enabled without the separate `.wiki.git` repository having been initialized**. The publishing job checks this before attempting synchronization.

1. Open the [semigeneric Wiki](https://github.com/shulda/lean_eppa_semigeneric/wiki) while signed in.
2. **Only if it asks to create the first page**, create a page titled **Home** with any temporary text (for example, “Automatically published from docs/wiki”), and save.
3. That edit normally triggers a `gollum` run. Otherwise open [Actions → Publish Semigeneric Wiki](https://github.com/shulda/lean_eppa_semigeneric/actions/workflows/publish-wiki.yml) and select **Run workflow** on `main`.
4. Verify that the publishing workflow actually reports pushing `Home.md` and the remaining pages to the Wiki's separate Git repository.

**Do not create a second Home page if one already exists.** This guide does not claim the Wiki is published until a real successful sync log confirms that fact.

## What the action does

- Checks out the current version-controlled pages and checks for the independent Wiki Git remote.
- Runs `Andrew-Chen-Wang/github-wiki-action@v5` with `preprocess: true` and `strategy: clone`.
- Publishes `docs/wiki/README.md` as the Wiki `Home.md` and copies the other Markdown pages, with a sidebar and fixed source code links.
- Uses GitHub's `contents: write` permission. Direct edits on the Wiki tab can be replaced by the automated source sync.

**Version-control policy:** edit mathematical claims in `docs/wiki/` through normal repository commits/PRs, *not* only through the GitHub Wiki web editor. That permits source review and audit history before publication. The private manuscript is **not** copied to the Wiki; only public Lean statements and this independently written mathematical exposition appear.

## Troubleshooting

If the workflow reports “Wiki not initialized”, complete the first-page creation step above. If it instead fails on Wiki push permissions, check repository Actions permissions and whether the GitHub token has access to the Wiki repository; leave `lean.yml` read-only. A successful source-control commit without a successful publishing job means that the **pages are ready in `docs/wiki`**, not necessarily live in the Wiki tab.
