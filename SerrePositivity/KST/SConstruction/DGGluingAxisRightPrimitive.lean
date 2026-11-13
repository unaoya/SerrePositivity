module
public import SerrePositivity.KST.SConstruction.DGGluingAxisRightComma
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Postcomposition

/-! # 元の右軸包含の後合成による比較 cochain の保存
概要：同じ右軸包含による全 Hom 後合成は、元の第三 cochain を厳密に保持する。
方針：元の代表加群 Hom 同型で移し、比較零と係数射恒等から元の cochain へ戻す。
規約：全整数次数の式。使われ方：標準二成分 cocone 包含との実比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (z : C) (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z))
  (T X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 元の右軸包含による後合成は、同じ全比較 cochain を保持する。 -/
lemma dgGluingAxisRightInclusion_post_primitive :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M T
      (dgGluingRightAxisObject R C D M z X.right) X
      (dgGluingAxisRightInclusion R C D M z hz X))).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M T X) (zero_add (-1)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M T (dgGluingRightAxisObject R C D M z X.right) := by
  apply cochainPostIso_injective (dgYonedaIso R T.left (M.rightAt X.right)).symm
  simp only [Iso.symm_hom]
  erw [Cochain.comp_assoc_of_third_is_zero_cochain,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_primitive R C D M T X,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_primitive R C D M T
      (dgGluingRightAxisObject R C D M z X.right),
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
  have hn := dgHomMap_postcompose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)
    (ForgetEnrichment.of (Complex R) T) (dgGluingAxisRightInclusion R C D M z hz X)
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M T
      (dgGluingRightAxisObject R C D M z X.right) X
      (dgGluingAxisRightInclusion R C D M z hz X) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M T X).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M T
      (dgGluingRightAxisObject R C D M z X.right)).hom ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M T))
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map
          (dgGluingAxisRightInclusion R C D M z hz X)) at hn
  rw [hn]
  erw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPost_of_comparison_zero R D (RightModule R C) M.toFunctor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M T)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M (dgGluingRightAxisObject R C D M z X.right))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map
      (dgGluingAxisRightInclusion R C D M z hz X))
    (dgGluingAxisRightInclusion_comma_comparison R C D M z hz X)]
  erw [dgGluingAxisRightInclusion_comma_image, eHomWhiskerLeft_id, Cochain.comp_id]
  rfl

end SerrePositivity.KST.SConstruction
