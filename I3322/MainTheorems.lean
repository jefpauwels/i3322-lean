import I3322.QuantumSupremum
import I3322.TableToPV
import I3322.OperatorReduction
import I3322.EqualityExtraction

/-!
# Theorems 1 and 2

`I3322/Statement.lean` gives the definitions and statements with references
to arXiv:2608.29734v1. The repository `README.md` gives the correspondence
between the paper and the Lean declarations.

Lemma 2 bounds every quantum value by a finite spectral-weight matrix;
Lemma 3 bounds its value by `betaPV`; Lemmas 4--5 exclude equality.
The final theorems supply the intermediate hypotheses, including
`tableBound`, with proved results.
-/

namespace I3322

/-- The spectral-weight bound implies that every quantum value is at most `betaPV`. -/
theorem quantumValue_le_betaPV_of_tableBound
    (tableBound : ∀ S : QuantumStrategy,
      ∃ θ : CouplingTable, S.value ≤ θ.score)
    (S : QuantumStrategy) :
    S.value ≤ betaPV := by
  obtain ⟨θ, hSθ⟩ := tableBound S
  exact hSθ.trans (CouplingTable.Ensemble.score_le_betaPV θ)

/-- The spectral-weight bound implies the upper inequality between the suprema. -/
theorem quantumSupremum_le_betaPV_of_tableBound
    (tableBound : ∀ S : QuantumStrategy,
      ∃ θ : CouplingTable, S.value ≤ θ.score) :
    quantumSupremum ≤ betaPV := by
  apply csSup_le quantumValues_nonempty
  rintro _ ⟨S, rfl⟩
  exact quantumValue_le_betaPV_of_tableBound tableBound S

/--
**Theorem 1 with the spectral-weight bound as an explicit hypothesis.**
-/
theorem quantumSupremum_eq_betaPV_of_tableBound
    (tableBound : ∀ S : QuantumStrategy,
      ∃ θ : CouplingTable, S.value ≤ θ.score) :
    quantumSupremum = betaPV :=
  le_antisymm (quantumSupremum_le_betaPV_of_tableBound tableBound)
    betaPV_le_quantumSupremum

/--
**Theorem 1 (the PV family gives the quantum supremum).**  The supremum of
the finite-dimensional quantum strategies is exactly the supremum of
the finite PV chains.
-/
theorem quantumSupremum_eq_betaPV : quantumSupremum = betaPV :=
  quantumSupremum_eq_betaPV_of_tableBound QuantumStrategy.tableBound

/-- Short name for the first main theorem. -/
theorem variational : quantumSupremum = betaPV :=
  quantumSupremum_eq_betaPV

/-- A hypothetical maximizing strategy forces equality for a matrix supplied by Lemma 2. -/
theorem equalityTable_of_quantumMaximizer_of_tableBound
    (tableBound : ∀ S : QuantumStrategy,
      ∃ θ : CouplingTable, S.value ≤ θ.score)
    (S : QuantumStrategy)
    (hS : S.value = quantumSupremum) :
    ∃ θ : CouplingTable, θ.score = betaPV := by
  obtain ⟨θ, hSθ⟩ := tableBound S
  refine ⟨θ, le_antisymm (CouplingTable.Ensemble.score_le_betaPV θ) ?_⟩
  calc
    betaPV = quantumSupremum :=
      (quantumSupremum_eq_betaPV_of_tableBound tableBound).symm
    _ = S.value := hS.symm
    _ ≤ θ.score := hSθ

/-! Nonattainment follows from the two proved bounds. -/

/--
**Theorem 2 with the spectral-weight bound and exclusion of equality as
explicit hypotheses.**
-/
theorem finiteDimensional_nonattainment_of_tableBound
    (tableBound : ∀ S : QuantumStrategy,
      ∃ θ : CouplingTable, S.value ≤ θ.score)
    (score_ne_betaPV : ∀ θ : CouplingTable, θ.score ≠ betaPV) :
    ∀ S : QuantumStrategy, S.value ≠ quantumSupremum := by
  intro S hS
  obtain ⟨θ, hθ⟩ :=
    equalityTable_of_quantumMaximizer_of_tableBound tableBound S hS
  exact score_ne_betaPV θ hθ

/--
**Theorem 2 (finite-dimensional nonattainment).** No
finite-dimensional pure-state/projective strategy attains `quantumSupremum`.
-/
theorem finiteDimensional_nonattainment :
    ∀ S : QuantumStrategy, S.value ≠ quantumSupremum :=
  finiteDimensional_nonattainment_of_tableBound
    QuantumStrategy.tableBound CouplingTable.score_ne_betaPV

end I3322
