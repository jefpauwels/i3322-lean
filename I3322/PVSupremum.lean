import I3322.CertifiedBounds
import I3322.PVUpperBound

/-!
# The coarse interval for the finite PV supremum
-/

namespace I3322

theorem pvValues_bddAbove : BddAbove (Set.range PVChain.value) :=
  PVUpperBound.values_bddAbove

theorem pvValues_nonempty : (Set.range PVChain.value).Nonempty :=
  ⟨CertifiedBounds.lowerCertificate.value,
    ⟨CertifiedBounds.lowerCertificate, rfl⟩⟩

theorem pvValue_le_betaPV (p : PVChain) : p.value ≤ betaPV := by
  exact le_csSup pvValues_bddAbove ⟨p, rfl⟩

theorem quarter_lt_betaPV : (1 / 4 : ℝ) < betaPV := by
  exact CertifiedBounds.quarter_lt_lowerCertificate_value.trans_le
    (pvValue_le_betaPV CertifiedBounds.lowerCertificate)

theorem betaPV_le_golden : betaPV ≤ (Real.sqrt 5 - 1) / 4 := by
  apply csSup_le pvValues_nonempty
  rintro _ ⟨p, rfl⟩
  exact PVUpperBound.value_le_golden p

theorem betaPV_lt_third : betaPV < (1 / 3 : ℝ) :=
  betaPV_le_golden.trans_lt PVUpperBound.golden_lt_third

end I3322
