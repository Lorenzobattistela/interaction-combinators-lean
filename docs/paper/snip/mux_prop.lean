theorem multiplexor_property
    (ts us : List (Term sig ℕ))
    (Δ : CNet)
    (hlen : ts.length = us.length) :
    Red (s(mux ts, muxStar us) ::ₘ Δ) (Wires ts us + Δ)
