import I3322.QuantumSupremum
import I3322.TableToPV
import I3322.OperatorReduction
import I3322.EqualityExtraction

/-!
# Assembly of the two main theorems

This file contains the order-theoretic assembly of the two main theorems using
`QuantumStrategy` and the definitions `quantumSupremum` and `betaPV`.

The first bridge says that every finite-dimensional quantum strategy is
bounded by a finite coupling table.  The second says that no coupling table
has score exactly `betaPV`.  Both bridges are proved in imported modules; the
lemmas below also expose parameterized assembly forms so that the final
dependency structure remains explicit.
-/

namespace I3322

/-- The sharp table reduction bounds every raw quantum value by `betaPV`. -/
theorem quantumValue_le_betaPV_of_tableBound
    (tableBound : ∀ S : QuantumStrategy,
      ∃ θ : CouplingTable, S.value ≤ θ.score)
    (S : QuantumStrategy) :
    S.value ≤ betaPV := by
  obtain ⟨θ, hSθ⟩ := tableBound S
  exact hSθ.trans (CouplingTable.Ensemble.score_le_betaPV θ)

/-- The sharp table reduction gives the upper inequality between the two
concrete suprema. -/
theorem quantumSupremum_le_betaPV_of_tableBound
    (tableBound : ∀ S : QuantumStrategy,
      ∃ θ : CouplingTable, S.value ≤ θ.score) :
    quantumSupremum ≤ betaPV := by
  apply csSup_le quantumValues_nonempty
  rintro _ ⟨S, rfl⟩
  exact quantumValue_le_betaPV_of_tableBound tableBound S

/--
**Theorem 1, assembly form.**  A sharp table reduction, together with the
already formalized explicit realization of every finite PV chain, identifies
the finite-dimensional quantum supremum with `betaPV`.
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

/-- A hypothetical maximizing strategy forces equality in one of the coupling
tables supplied by the sharp operator reduction. -/
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

/-! The second bridge is a direct proposition rather than a structure field. -/

/--
**Theorem 2, assembly form.**  The sharp table reduction and table-level
strictness imply that no finite-dimensional strategy attains the
quantum supremum.
-/
theorem finiteDimensional_nonattainment_of_bridges
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
finite-dimensional pure-projective strategy attains `quantumSupremum`.
-/
theorem finiteDimensional_nonattainment :
    ∀ S : QuantumStrategy, S.value ≠ quantumSupremum :=
  finiteDimensional_nonattainment_of_bridges
    QuantumStrategy.tableBound CouplingTable.score_ne_betaPV

end I3322
