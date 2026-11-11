# *Linear Algebra Done Right*, tagged with lean-cite

Chapter 1 of a Lean formalization of Axler's *Linear Algebra Done Right*, with each declaration and
proof step linked to the item of the book it formalizes, using
[lean-cite](https://github.com/Deicyde/lean-cite). The links export as
[Literature Links](https://github.com/mathlib-initiative/literature-links) annotations.

```lean
@[cite ladr4e "1.26"]
theorem unique_zero (z : V) (h : ∀ v, v + z = v) : z = 0 := …
```

## Branches

- [`wrappers`](https://github.com/Deicyde/linear-algebra-done-right-lean-cite/tree/wrappers):
  proof steps marked by wrappers (`cite ladr4e "1.26" step 2 =>`).
- [`comment-markers`](https://github.com/Deicyde/linear-algebra-done-right-lean-cite/tree/comment-markers):
  proof steps marked by comments (`-- cite ladr4e "1.26" step 2`).
- `main`: the formalization without tags.

## Export

On either tagged branch:

```sh
lake exe cache get
lake build
lake env lean CiteExport.lean
python3 .lake/packages/cite/scripts/cite_ll.py cite-export.json \
  --project https://github.com/Deicyde/linear-algebra-done-right-lean-cite \
  --commit "$(git rev-parse HEAD)" --out annotations/
```

This writes the links to `annotations/ladr4e.jsonl`.

## License

Apache-2.0.
