module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.TrivialFibrationHomotopy
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering

/-!
概要：二つの trivial Kan fibration の共通源で、片方の厳密な切断から比較のホモトピー逆を作る。
方針：各射の切断に対する基底上のホモトピーを前後から合成し、両側逆を一つずつ得る。
規約：単体集合自体の Kan 性は不要。使われ方：区間とホーンの重みの end の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 共通源からの二つの自明 fibration の一方の厳密な切断は、他方への同値を与える。 -/
lemma homotopyEquivalence_of_split_trivial_span {T I H : SSet.{u}}
    (r : T ⟶ I) (p : T ⟶ H) [TrivialKanFibration r] [TrivialKanFibration p]
    (s : I ⟶ T) (hs : s ≫ r = 𝟙 I) : IsSimplicialHomotopyEquivalence (s ≫ p) := by
  obtain ⟨t, ht⟩ := trivialKanFibration_exists_section p
  obtain ⟨Hp, _⟩ := exists_homotopy_over_trivialKanFibration p (p ≫ t) (𝟙 T) (by
    rw [Category.assoc, ht, Category.comp_id, Category.id_comp])
  obtain ⟨Hr, _⟩ := exists_homotopy_over_trivialKanFibration r (r ≫ s) (𝟙 T) (by
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
  refine ⟨t ≫ r, ?_, ?_⟩
  · have h := functorHomotopyPostcomp (functorHomotopyPrecomp Hp s) r
    simpa only [Category.assoc, Category.id_comp, Category.comp_id, hs] using Nonempty.intro h
  · have h := functorHomotopyPostcomp (functorHomotopyPrecomp Hr t) p
    simpa only [Category.assoc, Category.id_comp, Category.comp_id, ht] using Nonempty.intro h

end SerrePositivity.KST.Spectra
