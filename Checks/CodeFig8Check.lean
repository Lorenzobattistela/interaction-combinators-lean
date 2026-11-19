import InteractionCombinators.Lafont.Code

/-!
# The code and the decoder written out against Fig. 8 (page 88)

How Fig. 8 is read. Ports are numbered clockwise (page 71). A cell drawn pointing down lists its
auxiliary ports from left to right; a cell drawn pointing up has its first auxiliary port (Lean
port 0, Lafont's port 1) on the right, as in the numbered picture of page 82. `mux` (pointing down)
and `muxStar` (pointing up) both list their ports from left to right as drawn.

* **The code.** In the decomposition drawn above Fig. 8 the `dup` cells point up and the wires
  cross, so the left group of ports of `π'` receives the drawn left ports of the cells (Lean port
  1) and the right group their drawn right ports (Lean port 0). In Fig. 8 the four wires of `M_4`,
  from left to right, go to `M_n`, to the right `M_n*` (over the right group), to the left `M_n*`
  (over the left group) and to the root of `π'`. So
  `!π = M_4 [M_n (x_i), M_n* (trees on port 0), M_n* (trees on port 1), τ]`.
* **The decoder.** `M_4*` points up; its first port carries a `dup` cell pointing up, whose drawn
  right port (port 0) the inner loop joins to the second port of `M_4*`, and whose drawn left port
  (port 1) the outer loop joins to the third; the fourth is the free port. So
  `D = M_4* [dup(a, b), a, b, w]`, with `a` on port 0 of the `dup` cell.
-/

namespace INet.Comb.CodeFig8Check

open Term

/-- **The decoder of Fig. 8 (page 88), unfolded.** `M_4* [dup(k, k + 1), k, k + 1, w]`, nested as
`muxStar` is: the `dup` cell on the left (Lean port 1) of the root `con`, and the wire `k` (port 0
of the `dup` cell) on the next `con`, before `k + 1` (its port 1). -/
theorem decoder_unfold (w k : ℕ) : (decoder w k : Term sig ℕ) =
    mkCon (mkCon (mkCon (var w) (var (k + 1))) (var k)) (mkDup (var k) (var (k + 1))) := rfl

/-- The package `dup(con(0, 1), con(1, 0))` (page 88): one `dup` cell whose trees on port 0 and on
port 1 differ. -/
def π₁ : Term sig ℕ := mkDup (mkCon (var 0) (var 1)) (mkCon (var 1) (var 0))

/-- **The code of `π₁` (Fig. 8, page 88), unfolded.** New names from `2`: the cell is cut at `2`,
`τ = 2`, and `M_1` is a wire, so `!π₁ = M_4 [2, con(0, 1), con(1, 0), 2]`: the tree `con(0, 1)` on
port 0 of the cell sits on the second port of `M_4`, `con(1, 0)` on port 1 on the third. -/
theorem code_π₁_unfold : code 2 π₁ =
    mkCon (var 2) (mkCon (mkCon (var 0) (var 1)) (mkCon (mkCon (var 1) (var 0)) (var 2))) := rfl

/-- **The first stage of Fig. 9 (page 89) on `π₁`**, decoder with free port `9` and loop `5, 6`:
`M_4` against `M_4*` joins the cut name `2` to the `dup` cell, the tree on port 0, `con(0, 1)`, to
port 0 of that cell (`5`), the tree on port 1, `con(1, 0)`, to its port 1 (`6`), and `τ = 2` to
the free port `9`. -/
theorem code_decoder_π₁ : Red {s(code 2 π₁, decoder 9 5)}
    (s(var 2, mkDup (var 5) (var 6)) ::ₘ s(mkCon (var 0) (var 1), var 5) ::ₘ
      s(mkCon (var 1) (var 0), var 6) ::ₘ {s(var 2, var 9)}) :=
  code_decoder 2 π₁ 9 5 0

end INet.Comb.CodeFig8Check
