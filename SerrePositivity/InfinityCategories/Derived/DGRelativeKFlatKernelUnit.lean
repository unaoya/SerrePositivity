module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelNerve
public import SerrePositivity.InfinityCategories.Derived.DGKernelIdentityInfinity
public import SerrePositivity.InfinityCategories.F1.FullyFaithfulIsoRecovery
/-!
概要：通常 K-flat kernel 作用の対角単位を、元の実 co-Yoneda 単位から回収する。
方針：元の生の nerve の指定単位を、完全充満な実包含を通じて持ち上げる。
規約：原 Hom の平坦性を追加しない。使われ方：K-flat の単位・合成 coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v)
  [DGCategory R D] [Small.{u} D]
/-- 同じ通常対角 kernel の K-flat 作用は、元の co-Yoneda 単位によって恒等と同型。 -/
def dgRelativeKFlatKernelIdentityIso :
    FunctorIso (dgRelativeKFlatKernelNerve R D D (Bimodule.diagonal R D)
      (Bimodule.diagonal_rightRelativeKFlat R D)) (𝟙 (dgRelativeKFlatModuleNerve R D)) := by
  have e : FunctorIso
      (dgRelativeKFlatKernelNerve R D D (Bimodule.diagonal R D)
        (Bimodule.diagonal_rightRelativeKFlat R D) ≫ dgRelativeKFlatModuleInclusion R D)
      ((𝟙 (dgRelativeKFlatModuleNerve R D)) ≫ dgRelativeKFlatModuleInclusion R D) := by
    rw [dgRelativeKFlatKernelNerve_inclusion, Category.id_comp]
    simpa only [Category.comp_id] using!
      (dgKernelIdentityNerveIso R D).precomp (dgRelativeKFlatModuleInclusion R D)
  exact (isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R D)
    (dgModuleRelativeKFlatVertex R D)).preimageFunctorIso e
/-- K-flat の指定単位は、実包含後に元の co-Yoneda 単位の同じ値を回収する。 -/
lemma dgRelativeKFlatKernelIdentityIso_inclusion_heq :
    HEq ((dgRelativeKFlatKernelIdentityIso R D).postcomp
      (dgRelativeKFlatModuleInclusion R D))
      ((dgKernelIdentityNerveIso R D).precomp (dgRelativeKFlatModuleInclusion R D)) := by
  dsimp -zeta only [dgRelativeKFlatKernelIdentityIso]
  extract_lets e
  have hf : IsFullyFaithful (dgRelativeKFlatModuleInclusion R D) :=
    isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R D) (dgModuleRelativeKFlatVertex R D)
  have h := hf.preimageFunctorIso_postcomp e
  apply (heq_of_eq h).trans
  simp only [e, Eq.mpr]
  rfl
end SerrePositivity.InfinityCategories
