import InteractionCombinators.Universality.RecursionFree.PlugTr
import InteractionCombinators.Universality.RecursionFree.RecursionFreeTr
import InteractionCombinators.Universality.Multiplexors.TranspositorPerm
import InteractionCombinators.Text.Instance
import InteractionCombinators.Text.RenameMany

/-!
# Two cells of the translation meet (Fig. 7, rows 1 and 2, page 86)

Lafont 1997, Section 2.4, journal page 86 (PDF page 18).

* Renaming lemmas: `bind_mux`, `bind_muxStar`, `bind_transpositor`, `bind_transpositorPerm`,
  `bind_cellSkel`, `PNet.inst_bind_var`, `Translation.trTerm_shift`, `gamma_shift`. Renaming the
  names of a package `Γ` built from `k₀` by a function that shifts the names above `k₀` gives the
  same package built from the shifted name.
* `cellMenuAt`, `inst_cellNet` — an instance of `[α]` whose internal wire `w` is named `K + w` is
  the tree `cellSkel` of Fig. 6 with the menu built from `K + 1` and the loop `K`.
* `rawψ_self`, `rawSide_swap_of_rule` — for a rule `α`–`β`, the side of `β` against `α` is the
  `ψ` of its decomposition (page 86, `φ_{j,i} = ψ_{i,j}`), also when `α = β`.
* `translation_cells_meet` — **rows 1 and 2 of Fig. 7 for `D.translation`**: the two cells,
  plugged by their roots, reduce up to wires to the multiplexors against the packages `Γ` of the
  sides `φ` and `ψ` of the rule, in the form that `mux_gamma_mux_gamma_netTr` takes.
* `translation_cells_netTr_plug` — the two together: a translation of an instance of
  `Rule.plug φ ψ σ`.
-/

namespace INet

open Term

variable {S : Signature}

theorem PNet.inst_bind_var {n : ℕ} (p : PNet S n) (args : Fin n → Term S ℕ)
    (F : Fin p.internal → ℕ) (g : ℕ → ℕ) :
    (p.inst args F).bind (fun x => var (g x)) =
      p.inst (fun i => (args i).bind fun x => var (g x)) (fun w => g (F w)) := by
  rw [PNet.inst, PNet.inst, Term.bind_bind]
  congr 1
  funext q
  cases q <;> rfl

namespace Translation

variable {S' : Signature}

/-- The size of the translation of a tree does not change when its leaves are renamed. -/
theorem size_bind_var' (Φ : Translation S S') (t : Term S ℕ) (g : ℕ → ℕ) :
    Φ.size (t.bind fun x => var (g x)) = Φ.size t := by
  have := size_bind_var Φ t g id
  rw [this]
  simp only [id]
  rw [Term.bind_var_self]

/-- **Shifting the names of `trTerm`** (pages 79–80): renaming by `g`, which sends the new names
`k + i` to `k' + i`, the translation of `t` built from `k` is the translation of the renamed tree
built from `k'`. -/
theorem trTerm_shift (Φ : Translation S S') (g : ℕ → ℕ) :
    ∀ (t : Term S ℕ) (k k' : ℕ), (∀ i, g (k + i) = k' + i) →
      (Φ.trTerm k t).bind (fun x => var (g x)) = Φ.trTerm k' (t.bind fun x => var (g x))
  | .var x, _, _, _ => rfl
  | .app α ts, k, k', hg => by
    have hs : (fun j => Φ.size ((ts j).bind fun x => var (g x))) = fun j => Φ.size (ts j) :=
      funext fun j => size_bind_var' Φ _ g
    change ((Φ.net α).inst _ (fun w => k + w)).bind _ =
      (Φ.net α).inst (fun i => Φ.trTerm (k' + (Φ.net α).internal +
        off (fun j => Φ.size ((ts j).bind fun x => var (g x))) i)
          ((ts i).bind fun x => var (g x))) (fun w => k' + w)
    rw [PNet.inst_bind_var, hs]
    congr 1
    · funext i
      refine trTerm_shift Φ g (ts i) _ _ fun j => ?_
      rw [show k + (Φ.net α).internal + off (fun j => Φ.size (ts j)) i + j =
        k + ((Φ.net α).internal + off (fun j => Φ.size (ts j)) i + j) by omega, hg]
      omega
    · funext w
      exact hg w

end Translation

namespace Comb

open Translation

/-- Renaming goes through the multiplexor `M_n`. -/
theorem bind_mux (f : ℕ → Term sig ℕ) :
    ∀ (us : List (Term sig ℕ)), (mux us).bind f = mux (us.map (·.bind f))
  | [] => by simp [mux]
  | [_] => rfl
  | u :: u' :: us => by
    rw [mux, bind_mkCon, bind_mux f (u' :: us)]
    rfl

/-- Renaming goes through the dual multiplexor `M_n*`. -/
theorem bind_muxStar (f : ℕ → Term sig ℕ) :
    ∀ (us : List (Term sig ℕ)), (muxStar us).bind f = muxStar (us.map (·.bind f))
  | [] => by simp [muxStar]
  | [_] => rfl
  | u :: u' :: us => by
    rw [muxStar, bind_mkCon, bind_muxStar f (u' :: us)]
    rfl

/-- Renaming goes through the autodual multiplexor `T_n`. -/
theorem bind_autoMux (f : ℕ → Term sig ℕ) :
    ∀ (us : List (Term sig ℕ)), (autoMux us).bind f = autoMux (us.map (·.bind f))
  | [] => by simp [autoMux]
  | [_] => rfl
  | u :: u' :: us => by
    rw [autoMux, bind_mkDup, bind_autoMux f (u' :: us)]
    rfl

theorem map_bind_pairCon (f : ℕ → Term sig ℕ) :
    ∀ (p : ℕ) (us : List (Term sig ℕ)),
      (pairCon p us).map (·.bind f) = pairCon p (us.map (·.bind f))
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | _ + 1, [_] => rfl
  | p + 1, u :: u' :: us => by
    simp only [pairCon, List.map_cons, bind_mkCon, map_bind_pairCon f p us]

/-- Renaming goes through the transpositor `T_{p,q}`. -/
theorem bind_transpositor (f : ℕ → Term sig ℕ) (p : ℕ) (us : List (Term sig ℕ)) :
    (transpositor p us).bind f = transpositor p (us.map (·.bind f)) := by
  rw [transpositor, bind_autoMux, map_bind_pairCon, transpositor]

/-- Renaming goes through the transpositor `T_σ`. -/
theorem bind_transpositorPerm {n : ℕ} (f : ℕ → Term sig ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : Function.Involutive σ) (ts : Fin n → Term sig ℕ) :
    (transpositorPerm σ hσ ts).bind f = transpositorPerm σ hσ fun j => (ts j).bind f := by
  rw [transpositorPerm, bind_transpositor, List.map_map, transpositorPerm]
  rfl

/-- Renaming goes through the selector with a tree on its free port. -/
theorem bind_cellSel (f : ℕ → Term sig ℕ) (m i : ℕ) (t : Term sig ℕ) :
    (cellSel m i t).bind f = cellSel m i (t.bind f) := by
  simp [cellSel, bind_muxStar, List.map_replicate]

/-- **Renaming the cell `[αᵢ]` of Fig. 6** (page 86): renaming by `g` renames the menu, the trees on
the auxiliary ports and the loop. -/
theorem bind_cellSkel (g : ℕ → ℕ) (Γ : Term sig ℕ) (m i : ℕ) (ts : List (Term sig ℕ)) (ℓ : ℕ) :
    (cellSkel Γ m i ts ℓ).bind (fun x => var (g x)) =
      cellSkel (Γ.bind fun x => var (g x)) m i (ts.map (·.bind fun x => var (g x))) (g ℓ) := by
  simp [cellSkel, bind_transpositor, bind_cellSel, bind_mux]

variable {a k : ℕ}

/-- Shifting the names of the tree of `φ` at a port. -/
theorem gammaTree_shift (φ : Rule S a k) (g : ℕ → ℕ) (k₀ k₀' : ℕ) (hg : ∀ i, g (k₀ + i) = k₀' + i)
    (p : Fin a ⊕ Fin k) :
    (gammaTree φ k₀ p).bind (fun x => var (g x)) = gammaTree φ k₀' p := by
  rw [gammaTree, gammaTree, Term.bind_bind]
  congr 1
  funext x
  rcases x with x | x | w
  · change var (g k₀) = var k₀'
    simpa using hg 0
  · change var (g k₀) = var k₀'
    simpa using hg 0
  · change var (g (k₀ + w)) = var (k₀' + w)
    rw [hg]

/-- The sizes of the trees of `[φ]` do not depend on the first name. -/
theorem gammaSizes_eq (Φ : Translation S sig) (φ : Rule S a k) (k₀ k₀' : ℕ) :
    gammaSizes Φ φ k₀ = gammaSizes Φ φ k₀' :=
  funext fun _ => size_bind_var Φ _ _ _

/-- Shifting the names of the tree of `[φ]` at a port. -/
theorem gammaPort_shift (Φ : Translation S sig) (φ : Rule S a k) (g : ℕ → ℕ) (k₀ k₀' : ℕ)
    (hg : ∀ i, g (k₀ + i) = k₀' + i) (p : Fin a ⊕ Fin k) :
    (gammaPort Φ φ k₀ p).bind (fun x => var (g x)) = gammaPort Φ φ k₀' p := by
  rw [gammaPort, gammaPort, trTerm_shift Φ g _ _
    (k₀' + φ.internal + off (gammaSizes Φ φ k₀') (finSumFinEquiv p)) ?_,
    gammaTree_shift φ g k₀ k₀' hg]
  intro i
  rw [show k₀ + φ.internal + off (gammaSizes Φ φ k₀) (finSumFinEquiv p) + i =
    k₀ + (φ.internal + off (gammaSizes Φ φ k₀) (finSumFinEquiv p) + i) by omega, hg,
    gammaSizes_eq Φ φ k₀ k₀']
  omega

/-- **Shifting the names of `Γ_{i,j}`** (Fig. 6, page 86): renaming by `g`, which sends `k₀ + i`
to `k₀' + i`, the package built from `k₀` becomes the package built from `k₀'`. -/
theorem gamma_shift (Φ : Translation S sig) (φ : Rule S a k) (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ) (g : ℕ → ℕ) (k₀ k₀' : ℕ) (hg : ∀ i, g (k₀ + i) = k₀' + i) :
    (gamma Φ φ σ hσ k₀).bind (fun x => var (g x)) = gamma Φ φ σ hσ k₀' := by
  rw [gamma, gamma, bind_muxStar, List.map_append, List.map_ofFn, List.map_cons, List.map_nil,
    bind_transpositorPerm]
  simp only [Function.comp_def, gammaPort_shift Φ φ g k₀ k₀' hg]

/-- Shifting the names of `gammaOpt`: renaming by `g`, which sends `k₀ + i` to `k₀' + i`. -/
theorem gammaOpt_shift (Φ : Translation S sig) (o : Option (ExpSide S a)) (g : ℕ → ℕ)
    (k₀ k₀' : ℕ) (hg : ∀ i, g (k₀ + i) = k₀' + i) :
    (gammaOpt Φ o k₀).bind (fun x => var (g x)) = gammaOpt Φ o k₀' := by
  cases o with
  | none => simp [gammaOpt]
  | some s => exact gamma_shift Φ s.φ s.σ s.involutive g k₀ k₀' hg

/-! ## The instance of `[α]` with its internal wires on a block of names -/

variable [Finite S.Sym] {I : System S}

/-- The menu of `[α]` with its packages built from `K + 1` instead of `n + 1`: the menu of an
instance of `[α]` whose internal wires are named `K, K + 1, …` (page 86). -/
noncomputable def cellMenuAt (Φ : Translation S sig) (D : I.RecursionFreeData) (α : S.Sym)
    (K : ℕ) : List (Term sig ℕ) :=
  List.ofFn fun i => gammaOpt Φ (D.side ((symEnum S).symm i) α) (K + 1 + off (cellSizes Φ D α) i)

/-- **An instance of the cell `[α]` of Fig. 6** (page 86): with the names `xs` on its auxiliary
ports and its internal wire `w` named `K + w`, it is the tree `cellSkel` of the menu built from
`K + 1`, the selector of `α`, the leaves `xs` and the loop `K`. -/
theorem inst_cellNet (Φ : Translation S sig) (D : I.RecursionFreeData) (α : S.Sym)
    (p : PNet sig (S.arity α)) (hp : p = cellNet Φ D α) (xs : Fin (S.arity α) → ℕ) (K : ℕ)
    (F : Fin p.internal → ℕ) (hF : ∀ w, F w = K + (w : ℕ)) :
    p.inst (fun i => var (xs i)) F =
      cellSkel (menu (cellMenuAt Φ D α K)) (Nat.card S.Sym) (symEnum S α)
        (List.ofFn fun j => var (xs j)) K := by
  subst hp
  let n := S.arity α
  let Itot := ∑ i, cellSizes Φ D α i
  let ρ : ℕ → ℕ := fun x => if h : x < n then xs ⟨x, h⟩ else K + (x - n)
  have hv := vars_cellSkel_ports n (Nat.card S.Sym) (symEnum S α) Itot _ (vars_menu_cellMenu Φ D α)
  change Term.bind (Sum.elim (fun i => var (xs i)) (fun w : Fin (Itot + 1) => var (F w)))
    ((cellSkel (menu (cellMenu Φ D α)) (cellMenu Φ D α).length (symEnum S α)
      (List.ofFn fun j : Fin n => var (j : ℕ)) n).bind fun x => var (cellName n Itot x)) = _
  rw [Term.bind_bind, show (cellMenu Φ D α).length = Nat.card S.Sym by simp [cellMenu]]
  rw [Term.bind_congr (g := fun x => var (ρ x)) ?_]
  · rw [bind_cellSkel, menu, menu, bind_mux, cellMenu, cellMenuAt, List.map_ofFn, List.map_ofFn]
    have hρn : ρ n = K := by simp [ρ]
    rw [hρn]
    congr 2
    · congr 1
      funext i
      simp only [Function.comp_apply]
      rw [Term.bind_congr (g := fun x => var (K + (x - n))) ?_]
      · exact gammaOpt_shift Φ _ _ _ _ fun j => by omega
      · intro x hx
        rw [vars_gammaOpt] at hx
        have := (Multiset.mem_Ico.1 (Multiset.mem_of_mem_nsmul hx)).1
        simp only [ρ, dite_eq_right (show ¬ x < n by omega)]
    · funext j
      simp [ρ]
  · intro x hx
    rw [hv] at hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · have hxn := (Multiset.mem_Ico.1 hx).2
      simp [ρ, cellName, hxn]
    · have hxn := Multiset.mem_Ico.1 (Multiset.mem_of_mem_nsmul hx)
      simp only [Term.bind, ρ, cellName, dite_eq_right (show ¬ x < n by omega),
        dite_eq_left (show x - n < Itot + 1 by omega), Sum.elim_inr]
      exact congrArg var (hF _)

/-- The packages of `cellMenuAt` are packages (page 80): an eraser, or `Γ` of a linear side in
expanded form (`gamma_isPackage`). -/
theorem isPackage_cellMenuAt (Φ : Translation S sig) (D : I.RecursionFreeData) (α : S.Sym)
    (K : ℕ) : ∀ π ∈ cellMenuAt Φ D α K, π.IsPackage := by
  intro π hπ
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hπ
  cases D.side ((symEnum S).symm i) α with
  | none => exact isPackage_mkEra
  | some s => exact gamma_isPackage Φ s.expanded s.linear s.σ s.involutive _

/-- The package of `β` in the menu of `[α]` built from `K + 1` (page 86). -/
theorem getElem_cellMenuAt (Φ : Translation S sig) (D : I.RecursionFreeData) (α β : S.Sym)
    (K : ℕ) (h : (symEnum S β : ℕ) < (cellMenuAt Φ D α K).length) :
    (cellMenuAt Φ D α K)[(symEnum S β : ℕ)]'h =
      gammaOpt Φ (D.side β α) (K + 1 + off (cellSizes Φ D α) (symEnum S β)) := by
  simp only [cellMenuAt, List.getElem_ofFn, Fin.eta]
  congr 2 <;> exact (symEnum S).symm_apply_apply β

end Comb

namespace PNet

variable {n : ℕ}

/-- A name of an instance is a name of a plugged tree or the name of an internal wire. -/
theorem mem_vars_inst (p : PNet S n) (args : Fin n → Term S ℕ) (F : Fin p.internal → ℕ)
    {z : ℕ} (hz : z ∈ (p.inst args F).vars) : (∃ i, z ∈ (args i).vars) ∨ ∃ w, z = F w := by
  rw [PNet.inst, Term.vars_bind, Multiset.mem_bind] at hz
  obtain ⟨q, -, hq⟩ := hz
  rcases q with i | w
  · exact .inl ⟨i, hq⟩
  · exact .inr ⟨w, by simpa using hq⟩

/-- The names of a plugged tree are names of the instance. -/
theorem mem_vars_inst_of_mem (p : PNet S n) (args : Fin n → Term S ℕ) (F : Fin p.internal → ℕ)
    {z : ℕ} (i : Fin n) (hz : z ∈ (args i).vars) : z ∈ (p.inst args F).vars := by
  rw [← Multiset.one_le_count_iff_mem, count_vars_inst]
  have h1 := Multiset.one_le_count_iff_mem.2 hz
  have hle : (args i).vars.count z ≤ ∑ i, (args i).vars.count z :=
    Finset.single_le_sum (f := fun i => (args i).vars.count z) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  omega

/-- The names of the internal wires are names of the instance. -/
theorem mem_vars_inst_internal (p : PNet S n) (args : Fin n → Term S ℕ)
    (F : Fin p.internal → ℕ) (w : Fin p.internal) : F w ∈ (p.inst args F).vars := by
  rw [← Multiset.one_le_count_iff_mem, count_vars_inst]
  have hle : (if F w = F w then 1 else 0) ≤ ∑ w', if F w = F w' then 1 else 0 :=
    Finset.single_le_sum (f := fun w' => if F w = F w' then 1 else 0) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ w)
  simp only [↓reduceIte] at hle
  omega

end PNet

namespace System.RecursionFreeData

variable {I : System S} (D : I.RecursionFreeData)

/-- For a rule `α`–`α`, the side `ψ` is the side `φ` (page 86, `φ_{i,i} = ψ_{i,i}`). -/
theorem rawψ_self {α : S.Sym} {r : Rule S (S.arity α) (S.arity α)} (h : I.rule α α = some r) :
    D.rawψ α α r h = D.rawφ α α r h := by
  have e := D.self α r h
  unfold rawψ rawφ
  congr 1

/-- **The side of `β` against `α`, for a rule `α`–`β`, is the `ψ` of its decomposition** (page 86,
`φ_{j,i} = ψ_{i,j}`). For `α ≠ β` there is no rule `β`–`α` (`WellFormed.unique`), so
`rawSide_of_rule_swap` applies; for `α = β` the side is `φ` (`rawSide_of_rule`), equal to `ψ` by
`D.self`. -/
theorem rawSide_swap_of_rule (hI : I.WellFormed) {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)} (h : I.rule α β = some r) :
    D.rawSide β α = some (D.rawψ β α r h) := by
  by_cases hab : α = β
  · subst hab
    rw [D.rawSide_of_rule h, D.rawψ_self h]
  · exact D.rawSide_of_rule_swap (hI.unique α β hab (by simp [h])) h

end System.RecursionFreeData

namespace Comb

open Term

variable [Finite S.Sym] {I : System S}

/-- **Two cells of the translation, plugged by their roots, meet** (Lafont 1997, Fig. 7, rows 1
and 2, page 86). For a well-formed recursion-free system and a rule `α`–`β`, the translations
`[α]` and `[β]` of `D.translation`, with the names `xs`, `ys` on their auxiliary ports and any
names `f`, `g` for their internal wires (the hypotheses of `Translation.Compatible`), reduce up to
wires to the multiplexor `M_{n+1}` with leaves `xs` and a loop `ℓ` against the package `Γ` of the
side `φ` of the rule, and `M_{m+1}` with leaves `ys` and the same loop against the package `Γ` of
the side `ψ`, both with the involution `σ` of the decomposition. This is the input of
`mux_gamma_mux_gamma_netTr`, whose hypothesis `hlin` is the last conjunct.

The selector of `[α]` extracts from the menu of `[β]` the package `Γ_{α,β}`, built from the side
of `α` against `β`: the `φ` of the rule `α`–`β` (`rawSide_of_rule`). The selector of `[β]`
extracts from the menu of `[α]` the package `Γ_{β,α}`, built from the side of `β` against `α`:
by `φ_{j,i} = ψ_{i,j}` (page 86) it is the `ψ` of the rule `α`–`β`, through
`rawSide_of_rule_swap` when `α ≠ β` (there is no rule `β`–`α`, `WellFormed.unique`) and through
`D.self` (`φ_{i,i} = ψ_{i,i}`) when `α = β`.

The internal wires of both instances are first renamed to blocks above every name of the net
(`PNet.equiv_inst_fresh`); the instances are then the trees `cellSkel` of Fig. 6 with their menus
shifted (`inst_cellNet`), and `cellSkel_cellSkel` applies. -/
theorem translation_cells_meet (hI : I.WellFormed) (D : I.RecursionFreeData) {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)} (h : I.rule α β = some r)
    (xs : Fin (S.arity α) → ℕ) (ys : Fin (S.arity β) → ℕ)
    (f : Fin (D.translation.net α).internal → ℕ) (g : Fin (D.translation.net β).internal → ℕ)
    (hlin : Net.Linear ({s((D.translation.net α).inst (fun i => .var (xs i)) f,
      (D.translation.net β).inst (fun j => .var (ys j)) g)} : CNet)) :
    ∃ (M : CNet) (k₀ k₁ ℓ : ℕ),
      StepsE system {s((D.translation.net α).inst (fun i => .var (xs i)) f,
        (D.translation.net β).inst (fun j => .var (ys j)) g)} M ∧
      Equiv M
        (s(mux (List.ofFn (fun p => (var (xs p) : Term sig ℕ)) ++ [var ℓ]),
            gamma D.translation (D.rawφ α β r h).expand.φ (D.dec α β r h).σ
              (D.involutive α β r h) k₀) ::ₘ
          s(mux (List.ofFn (fun q => (var (ys q) : Term sig ℕ)) ++ [var ℓ]),
            gamma D.translation (D.rawψ β α r h).expand.φ (D.dec α β r h).σ
              (D.involutive α β r h) k₁) ::ₘ 0) ∧
      Net.Linear
        (s(mux (List.ofFn (fun p => (var (xs p) : Term sig ℕ)) ++ [var ℓ]),
            gamma D.translation (D.rawφ α β r h).expand.φ (D.dec α β r h).σ
              (D.involutive α β r h) k₀) ::ₘ
          s(mux (List.ofFn (fun q => (var (ys q) : Term sig ℕ)) ++ [var ℓ]),
            gamma D.translation (D.rawψ β α r h).expand.φ (D.dec α β r h).σ
              (D.involutive α β r h) k₁) ::ₘ 0) := by
  let A := D.translation.net α
  let B := D.translation.net β
  let N : CNet := {s(A.inst (fun i => .var (xs i)) f, B.inst (fun j => .var (ys j)) g)}
  let K := (Net.vars N).sup + 1
  have hK : ∀ y ∈ Net.vars N, y < K := fun y hy => by
    have := Multiset.le_sup hy
    omega
  have hxs : ∀ i, xs i < K := fun i => hK _ (by
    simp only [N, Net.vars_singleton, eqVars_mk, Multiset.mem_add]
    exact .inl (PNet.mem_vars_inst_of_mem A _ f i (by simp)))
  have hys : ∀ j, ys j < K := fun j => hK _ (by
    simp only [N, Net.vars_singleton, eqVars_mk, Multiset.mem_add]
    exact .inr (PNet.mem_vars_inst_of_mem B _ g j (by simp)))
  have hg : ∀ w, g w < K := fun w => hK _ (by
    simp only [N, Net.vars_singleton, eqVars_mk, Multiset.mem_add]
    exact .inr (PNet.mem_vars_inst_internal B _ g w))
  let K' := K + A.internal
  let f' : Fin A.internal → ℕ := fun w => K + (w : ℕ)
  let g' : Fin B.internal → ℕ := fun w => K' + (w : ℕ)
  -- rename the internal wires of `[α]` to the block `K, K + 1, …`
  have E1 : Equiv N {s(A.inst (fun i => .var (xs i)) f', B.inst (fun j => .var (ys j)) g)} := by
    have L : Net.Linear (s(B.inst (fun j => .var (ys j)) g, A.inst (fun i => .var (xs i)) f)
        ::ₘ 0) := by
      rw [Sym2.eq_swap]
      exact hlin
    have E := PNet.equiv_inst_fresh (h := f') L (fun a b hab => Fin.ext (by simpa [f'] using hab))
      (fun w hw => by
        have : K + (w : ℕ) < K := hK _ (by
          simp only [N, Net.vars_singleton, Net.vars_cons, Net.vars_zero, add_zero,
            eqVars_mk] at hw ⊢
          rwa [add_comm])
        omega)
    rw [Sym2.eq_swap (a := B.inst _ g), Sym2.eq_swap (a := B.inst _ g)] at E
    exact E
  have L1 := E1.linear hlin
  -- rename the internal wires of `[β]` to the block `K', K' + 1, …`
  have E2 : Equiv {s(A.inst (fun i => .var (xs i)) f', B.inst (fun j => .var (ys j)) g)}
      {s(A.inst (fun i => .var (xs i)) f', B.inst (fun j => .var (ys j)) g')} := by
    refine PNet.equiv_inst_fresh (h := g') L1 (fun a b hab => Fin.ext (by simpa [g'] using hab))
      fun w hw => ?_
    have e1 : g' w = K' + (w : ℕ) := rfl
    have e2 : K' = K + A.internal := rfl
    simp only [Net.vars_cons, Net.vars_zero, add_zero, eqVars_mk, Multiset.mem_add] at hw
    rcases hw with hw | hw
    · rcases PNet.mem_vars_inst A _ f' hw with ⟨i, hi⟩ | ⟨w', hw'⟩
      · simp only [vars_var, Multiset.mem_singleton] at hi
        have := hxs i
        omega
      · have := w'.isLt
        have e3 : f' w' = K + (w' : ℕ) := rfl
        omega
    · rcases PNet.mem_vars_inst B _ g hw with ⟨j, hj⟩ | ⟨w', hw'⟩
      · simp only [vars_var, Multiset.mem_singleton] at hj
        have := hys j
        omega
      · have := hg w'
        omega
  -- the instances are cells of Fig. 6 with shifted menus
  have hA := inst_cellNet D.translation D α A (D.translation_net α) xs K f' fun _ => rfl
  have hB := inst_cellNet D.translation D β B (D.translation_net β) ys K' g' fun _ => rfl
  have L2 : Net.Linear
      (s(cellSkel (menu (cellMenuAt D.translation D α K)) (Nat.card S.Sym) (symEnum S α)
          (List.ofFn fun j => var (xs j)) K,
        cellSkel (menu (cellMenuAt D.translation D β K')) (Nat.card S.Sym) (symEnum S β)
          (List.ofFn fun j => var (ys j)) K') ::ₘ 0) := by
    rw [← hA, ← hB]
    exact E2.linear L1
  obtain ⟨M, hS, hE⟩ := cellSkel_cellSkel (cellMenuAt D.translation D α K)
    (cellMenuAt D.translation D β K') (Nat.card S.Sym) (symEnum S α) (symEnum S β)
    (by simp [cellMenuAt]) (by simp [cellMenuAt]) (Fin.isLt _) (Fin.isLt _)
    (isPackage_cellMenuAt _ D α K) (isPackage_cellMenuAt _ D β K') _ _ K K' 0 L2
  rw [getElem_cellMenuAt, getElem_cellMenuAt, D.side_eq, D.side_eq, D.rawSide_of_rule h,
    D.rawSide_swap_of_rule hI h] at hE
  rw [← hA, ← hB] at hS
  obtain ⟨M', hS', hE'⟩ := stepsE_of_equiv (E1.trans E2) hS
  have E := hE'.trans hE
  exact ⟨M', _, _, K, hS', E, E.linear (hS'.linear system_wellFormed.linear hlin)⟩

/-- **Fig. 7 for the translation, up to the plugged rule** (Lafont 1997, Fig. 7, page 86; the
plugged rule, page 85). `translation_cells_meet` followed by `mux_gamma_mux_gamma_netTr`: the two
cells of `D.translation` plugged by their roots reduce up to wires to a translation of an instance
of `Rule.plug φ ψ σ`, for the expanded sides `φ`, `ψ` and the involution `σ` of the decomposition
of the rule `α`–`β`, with the names `xs`, `ys` on its ports. -/
theorem translation_cells_netTr_plug (hI : I.WellFormed) (D : I.RecursionFreeData) {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)} (h : I.rule α β = some r)
    (xs : Fin (S.arity α) → ℕ) (ys : Fin (S.arity β) → ℕ)
    (f : Fin (D.translation.net α).internal → ℕ) (g : Fin (D.translation.net β).internal → ℕ)
    (hlin : Net.Linear ({s((D.translation.net α).inst (fun i => .var (xs i)) f,
      (D.translation.net β).inst (fun j => .var (ys j)) g)} : CNet)) :
    ∃ (M N' : CNet)
      (h' : Fin (Rule.plug (D.rawφ α β r h).expand.φ (D.rawψ β α r h).expand.φ
        (D.dec α β r h).σ).internal → ℕ),
      StepsE system {s((D.translation.net α).inst (fun i => .var (xs i)) f,
        (D.translation.net β).inst (fun j => .var (ys j)) g)} M ∧
      Equiv M N' ∧
      D.translation.NetTr ((Rule.plug (D.rawφ α β r h).expand.φ (D.rawψ β α r h).expand.φ
        (D.dec α β r h).σ).inst (fun i => .var (xs i)) (fun j => .var (ys j)) h') N' := by
  obtain ⟨M, k₀, k₁, ℓ, hS, hE, hL⟩ := translation_cells_meet hI D h xs ys f g hlin
  obtain ⟨M₂, N', h', hS₂, hE₂, hN'⟩ := mux_gamma_mux_gamma_netTr D.translation
    (D.rawφ α β r h).expand.expanded (D.rawφ α β r h).expand.linear
    (D.rawψ β α r h).expand.expanded (D.rawψ β α r h).expand.linear
    (D.dec α β r h).σ (D.involutive α β r h) k₀ k₁ xs ys ℓ hL
  obtain ⟨M', hS', hE'⟩ := stepsE_of_equiv hE hS₂
  exact ⟨M', N', h', hS.trans hS', hE'.trans hE₂, hN'⟩

end Comb

end INet
