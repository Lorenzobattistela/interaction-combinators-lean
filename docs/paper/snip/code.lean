def Decomp.code
    (D : Decomp) :
    Term sig ℕ :=
  mux [mux (D.cells.map fun c => var c.1), muxStar (D.cells.map fun c => c.2.1),
    muxStar (D.cells.map fun c => c.2.2), D.τ]

def decoder
    (w k : ℕ) :
    Term sig ℕ :=
  muxStar [mkDup (var k) (var (k + 1)), var k, var (k + 1), var w]
