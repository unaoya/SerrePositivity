module

public import SerrePositivity.EInfinity.BarrattEccles.DKHigherComponentsAgreement

/-!
# 元の実 Kan Hom 高次比較と保存済み π₀ 同値の一致

概要：元の Ex∞ 単位を通して、同じ Kan 比較の誘導同値を以前のものへ同定する。
方針：同じ単位の π₀ の全単射と raw 比較の全類での一致を使う。
規約：元の Kan 化・実 Hom・Map^h・元の射の類を保持する。
使われ方：E2b γ2 d の零次の整合の結論。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)

def cofibrantAlgebraKanDKHigherPiZeroEquiv :
    SSet.π₀ (SimplicialCategory.sHom
      (show CAlgSimplicialCategory A from cofibrantAlgebraDKObject A X)
      (show CAlgSimplicialCategory A from cofibrantAlgebraDKObject A Y)) ≃
        SSet.π₀ (((cofibrantAlgebraMappingSpace A).obj (op X)).obj Y) :=
  (cAlgMappingSpaceComponentsIso A
    (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y)).toEquiv.trans
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.equiv (((cofibrantAlgebraMappingSpace A).obj (op X)).obj Y))

lemma cofibrantAlgebraKanDKHigherPiZeroEquiv_unit
    (z : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom (cofibrantAlgebraRelativeCategory A)
      (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y))) :
    cofibrantAlgebraKanDKHigherPiZeroEquiv A X Y
        (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom (cofibrantAlgebraRelativeCategory A)
          (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y))) z) =
      cofibrantAlgebraDKHigherPiZeroEquiv A X Y z := by
  have h := ConcreteCategory.congr_hom (cAlgMappingSpaceComponentsIso_unit A
    (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y)) z
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.down (((cofibrantAlgebraMappingSpace A).obj (op X)).obj Y)) h

lemma cofibrantAlgebraKanDKHigherPiZeroEquiv_eq :
    cofibrantAlgebraKanDKHigherPiZeroEquiv A X Y = cofibrantAlgebraKanDKPiZeroEquiv A X Y := by
  apply Equiv.ext
  intro z
  let e := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomKanUnitPiZeroEquiv (cofibrantAlgebraRelativeCategory A)
    (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y)
  obtain ⟨t, rfl⟩ := e.surjective z
  change cofibrantAlgebraKanDKHigherPiZeroEquiv A X Y
      (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom (cofibrantAlgebraRelativeCategory A)
        (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y))) t) = _
  rw [cofibrantAlgebraKanDKHigherPiZeroEquiv_unit, cofibrantAlgebraDKHigherPiZeroEquiv_eq]
  change cofibrantAlgebraDKPiZeroEquiv A X Y t =
    cofibrantAlgebraDKPiZeroEquiv A X Y (e.symm (e t))
  rw [e.symm_apply_apply]

lemma cofibrantAlgebraDKHigherPiZeroEquiv_class {X Y : CofibrantAlgebra A} (f : X ⟶ Y) :
    cofibrantAlgebraDKHigherPiZeroEquiv A X Y
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowClass (cofibrantAlgebraRelativeCategory A)
          ((ULiftHom.up.{u, u + 1, u + 1} (C := CofibrantAlgebra A)).map f)) =
      mappingSpaceClass A ((cofibrantAlgebraInclusion A).map f) := by
  rw [cofibrantAlgebraDKHigherPiZeroEquiv_eq, cofibrantAlgebraDKPiZeroEquiv_class]

lemma cofibrantAlgebraKanDKHigherPiZeroEquiv_class {X Y : CofibrantAlgebra A} (f : X ⟶ Y) :
    cofibrantAlgebraKanDKHigherPiZeroEquiv A X Y
        (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom (cofibrantAlgebraRelativeCategory A)
          (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y)))
          (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowClass (cofibrantAlgebraRelativeCategory A)
            ((ULiftHom.up.{u, u + 1, u + 1} (C := CofibrantAlgebra A)).map f))) =
      mappingSpaceClass A ((cofibrantAlgebraInclusion A).map f) := by
  rw [cofibrantAlgebraKanDKHigherPiZeroEquiv_eq, cofibrantAlgebraKanDKPiZeroEquiv_class]

end SerrePositivity.EInfinity.BarrattEccles
