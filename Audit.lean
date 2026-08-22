import I3322.MainTheorems
import I3322.OperatorReduction
import I3322.FiniteSpine
import I3322.EqualityExtraction
import I3322.CertifiedBounds
import I3322.PVUpperBound
import I3322.Ensemble
import I3322.EqualityChain
import I3322.TableSymmetry
import I3322.FiniteCauchy
import I3322.ChainStationarity

/-!
# Axiom audit

Compile this file with `lake env lean Audit.lean`.  Lean prints the transitive
assumptions of the main theorems and supporting results.  They are limited to
the standard logical and quotient axioms used by Lean and mathlib.
-/

#print axioms I3322.CertifiedBounds.quarter_lt_lowerCertificate_value
#print axioms I3322.PVUpperBound.value_le_golden
#print axioms I3322.PVUpperBound.value_lt_third

#print axioms I3322.pvValue_le_betaPV
#print axioms I3322.quarter_lt_betaPV
#print axioms I3322.betaPV_le_golden
#print axioms I3322.betaPV_lt_third

#print axioms I3322.CouplingTable.Ensemble.walkEnsemble_diagonalMatches
#print axioms I3322.CouplingTable.Ensemble.walkEnsemble_junctionMatches
#print axioms I3322.CouplingTable.Ensemble.score_le_betaPV

#print axioms I3322.EqualityChain.false
#print axioms I3322.CouplingTable.mirrorScore_le_symmetrize_score
#print axioms I3322.re_dotProduct_star_le_sqrt_mul

#print axioms I3322.ChainStationarity.weighted_stationarity
#print axioms I3322.ChainStationarity.label_stationarity
#print axioms I3322.ChainStationarity.weighted_stationarity_of_finite_windows
#print axioms I3322.ChainStationarity.label_stationarity_of_finite_windows

#print axioms I3322.ValueSpine.clamped_label_stationarity
#print axioms I3322.ValueSpine.nonempty_equalityChain

#print axioms I3322.PVRealization.strategy_value
#print axioms I3322.PVRealization.schmidtStrategy_value
#print axioms I3322.PVRealization.exists_quantumStrategy
#print axioms I3322.PVRealization.exists_schmidtStrategy

#print axioms I3322.quantumValue_le_six
#print axioms I3322.quantumValues_bddAbove
#print axioms I3322.betaPV_le_quantumSupremum

#print axioms I3322.QuantumStrategy.value_le_raw_mirrorScore
#print axioms I3322.QuantumStrategy.tableBound

#print axioms I3322.CouplingTable.equalityChainOfTable
#print axioms I3322.CouplingTable.score_ne_betaPV
#print axioms I3322.CouplingTable.score_lt_betaPV

#print axioms I3322.quantumValue_le_betaPV_of_tableBound
#print axioms I3322.quantumSupremum_le_betaPV_of_tableBound
#print axioms I3322.quantumSupremum_eq_betaPV_of_tableBound
#print axioms I3322.equalityTable_of_quantumMaximizer_of_tableBound
#print axioms I3322.finiteDimensional_nonattainment_of_bridges

#print axioms I3322.quantumSupremum_eq_betaPV
#print axioms I3322.variational
#print axioms I3322.finiteDimensional_nonattainment
