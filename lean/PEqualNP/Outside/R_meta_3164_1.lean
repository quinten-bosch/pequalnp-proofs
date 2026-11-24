import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3164_1
    (smallGraph : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
          x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4)) 12)
    (restrict :
      ∀ C : Circuit, FanInTwo C →
        (∃ x : Fin 8 → Bool,
          C.eval (List.ofFn ((4 : Fin 9).insertNth false x)) ≠
            C.eval (List.ofFn ((4 : Fin 9).insertNth true x))) →
        (∃ x : Fin 8 → Bool, C.eval (List.ofFn ((4 : Fin 9).insertNth false x)) = false) →
        HasCircuitSize 8
          (fun x => C.eval (List.ofFn ((4 : Fin 9).insertNth false x))) (C.size - 1)) :
    ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ))) (13 : ℕ) := by
  let edge (x : Fin 9 → Bool) := (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  rintro ⟨C, hfan, hsize, hcompute⟩
  change ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edge x at hcompute
  have depends : ∃ x : Fin 8 → Bool,
      C.eval (List.ofFn ((4 : Fin 9).insertNth false x)) ≠
        C.eval (List.ofFn ((4 : Fin 9).insertNth true x)) := by
    refine ⟨fun i => decide (i = 0), ?_⟩
    rw [hcompute, hcompute]
    exact Bool.false_ne_true
  have negative : ∃ x : Fin 8 → Bool,
      C.eval (List.ofFn ((4 : Fin 9).insertNth false x)) = false := by
    refine ⟨fun _ => false, ?_⟩
    rw [hcompute]
    rfl
  obtain ⟨D, hD, hDs, hval⟩ := restrict C hfan depends negative
  apply smallGraph
  refine ⟨D, hD, by omega, ?_⟩
  intro x
  rw [hval]
  change C.eval (List.ofFn ((4 : Fin 9).insertNth false x)) = _
  rw [hcompute]
  change (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && false || false && x 0 ||
    x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 ||
    x 5 && x 7 || x 7 && x 4) = _
  simp only [Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or]
