/-- The form of Theorem 1 this project aimed at: the translation is strict. It implies `universal`
by `StrictlyUniversal.universal`. Lafont's translation has a cell at the root of every symbol
(Fig. 6 and Fig. 10), so it is strict. -/
theorem universal_strict :
    -- the system of `con`, `dup` and `era` is strictly universal: every interaction system over
    -- a finite alphabet has a translation into it that sends no symbol to a single wire
    -- (`StrictlyUniversal`, in `Core/Translation.lean`)
    StrictlyUniversal system
