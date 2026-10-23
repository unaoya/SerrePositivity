module
public import SerrePositivity.InfinityCategories.Derived.RestrictedDeformationInclusion
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelComparisonHom
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelComposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulIsoRecovery
/-!
概要：K-flat の変形円柱と通常 tensor の指定比較を、元の実包含上で回収する。
方針：全円柱の持ち上げの射影式と、完全充満包含の指定逆像の回収式を使う。
規約：元の指定値を保持する。使われ方：導来 kernel 合成子と通常作用の二経路の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
/-- K-flat の元の変形円柱は、実包含後に全加群の同じ円柱の制限へ戻る。 -/
lemma dgRelativeKFlatResolutionAugmentationHomotopy_ι :
    (dgRelativeKFlatResolutionAugmentationHomotopy R D).h ≫
      dgRelativeKFlatModuleInclusion R D =
    (functorHomotopyPrecomp (dgModuleResolutionAugmentationHomotopy R D)
      (dgRelativeKFlatModuleInclusion R D)).h := by
  exact deformationRestrictedHomotopy_ι _ _ _ _ _
/-- K-flat の指定通常合成比較は、実包含後に元の通常 tensor 比較の同じ値を回収する。 -/
lemma dgRelativeKFlatKernelCompositionIso_inclusion_heq
    (P : Bimodule R E D) (Q : Bimodule R K E)
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (hQ : Bimodule.rightRelativeKFlat R K E Q) :
    HEq ((dgRelativeKFlatKernelCompositionIso R D E K P Q hP hQ).postcomp
      (dgRelativeKFlatModuleInclusion R K))
      ((dgKernelTensorCompositionNerveIso R D E K P Q).precomp
        (dgRelativeKFlatModuleInclusion R D)) := by
  dsimp -zeta only [dgRelativeKFlatKernelCompositionIso]
  extract_lets e
  have hf : IsFullyFaithful (dgRelativeKFlatModuleInclusion R K) :=
    isFullyFaithful_fullSubcomplexOnVertices_ι (dgModuleNerve R K) (dgModuleRelativeKFlatVertex R K)
  have h := hf.preimageFunctorIso_postcomp e
  apply (heq_of_eq h).trans
  simp only [e, Eq.mpr]
  rfl
end SerrePositivity.InfinityCategories
