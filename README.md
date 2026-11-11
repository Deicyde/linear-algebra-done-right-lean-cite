# lean-cite demo: *Linear Algebra Done Right*

Rado Kirov's [Lean companion to *Linear Algebra Done Right*](https://github.com/rkirov/linear-algebra-done-right-lean),
with chapter 1's links to the book written into the Lean with
[lean-cite](https://github.com/Deicyde/lean-cite). For the companion itself, what it covers and how
to work through it, see Rado's repository.

```lean
@[cite ladr4e "1.26"]
theorem unique_zero (z : V) (h : ∀ v, v + z = v) : z = 0 := …
```

## Branches

- `main`: Rado's companion at `94a528c`, with this README.
- [`wrappers`](https://github.com/Deicyde/linear-algebra-done-right-lean-cite/tree/wrappers):
  chapter 1 tagged with `@[cite]`, and proof steps marked by wrappers
  (`cite ladr4e "1.26" step 2 =>`).
- [`comment-markers`](https://github.com/Deicyde/linear-algebra-done-right-lean-cite/tree/comment-markers):
  the same tags, with proof steps marked by comments (`-- cite ladr4e "1.26" step 2`).

## Exporting the links

On either branch:

```sh
lake exe cache get
lake build
lake env lean CiteExport.lean
python3 .lake/packages/cite/scripts/cite_ll.py cite-export.json \
  --project https://github.com/Deicyde/linear-algebra-done-right-lean-cite \
  --commit "$(git rev-parse HEAD)" --out annotations/
```

This writes `annotations/ladr4e.jsonl`, the links as
[Literature Links](https://github.com/mathlib-initiative/literature-links) annotations. lean-cite's
[`examples/ladr`](https://github.com/Deicyde/lean-cite/tree/main/examples/ladr) checks them against
the existing companion's annotations.

## License

Apache-2.0, as for Rado's companion.
