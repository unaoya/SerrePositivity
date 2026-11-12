module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonFamilyLift
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration
public import SerrePositivity.DifferentialGraded.Functor.Closed
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalDG
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence

/-!
概要：固定 ε 整合関手圏の横合成を、同じ正本商関手の横合成から構成する。
方針：等号移送した商上の全 Hom 作用を元の全対象評価で比較する。
規約：零単体への制限ではなく Hom 複体全体を扱う。
使われ方：商作用の全単体の横合成則。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory Limits MonoidalCategory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R]
  (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  (E : Type t) [DGCategory R E] [Small.{u} E]
  (S : Set C) (T : Set D) (U : Set E)
local instance : HasProductsOfShape C (ModuleCat.{u} R) := ModuleCat.hasLimitsOfShape

/-- 元の null 保存関手の横合成を全 Hom で取る。 -/
def quotientEpsilonHorizontalUnderlying :
    DGFunctor R (DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R D E T U)) (DGFunctor R C E) :=
  ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C D S T).tensor
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R D E T U)).comp (dgFunctorHorizontalDG R C D E)

/-- 合成された元の関手は同じ指定部分集合を保存する。 -/
lemma quotientEpsilonHorizontal_preserves
    (x : DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R D E T U)) :
    ∀ c ∈ S, ((quotientEpsilonHorizontalUnderlying R C D E S T U).obj x).obj c ∈ U :=
  fun c hc => x.2.property _ (x.1.property c hc)

/-- 同じ元の合成関手と null 保存証明を持つ対象。 -/
abbrev quotientEpsilonHorizontalObject
    (x : DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R D E T U)) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonFamilyObject R C E S U _
    (quotientEpsilonHorizontalUnderlying R C D E S T U)
    (quotientEpsilonHorizontal_preserves R C D E S T U) x

/-- 合成対象の正本商は、元の二つの正本商の厳密合成。 -/
lemma quotientEpsilonHorizontal_object
    (x : DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R D E T U)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C E S U
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonFamilyObject R C E S U _
        (quotientEpsilonHorizontalUnderlying R C D E S T U)
        (quotientEpsilonHorizontal_preserves R C D E S T U) x) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T x.1).comp
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R D E T U x.2) :=
  DGQuotient.quotientDGFunctor_comp R C D x.1.val S T x.1.property E x.2.val U x.2.property

/-- 商上の横 Hom 作用を同じ合成対象の正本値へ移送する。 -/
def quotientEpsilonHorizontalExtension
    (x y : DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R D E T U)) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension R C D S T x.1 y.1 ⊗ₘ
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension R D E T U x.2 y.2) ≫
    dgFunctorHorizontal R _ _ _
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T x.1) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T y.1)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R D E T U x.2) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R D E T U y.2) ≫
    dgFunctorHomTransport R _ _
      (quotientEpsilonHorizontal_object R C D E S T U x).symm
      (quotientEpsilonHorizontal_object R C D E S T U y).symm

/-- 横合成の商上の作用は、元の横合成と各対象で厳密に同じ成分を持つ。 -/
lemma quotientEpsilonHorizontal_components
    (x y : DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R D E T U)) :
    (quotientEpsilonHorizontalUnderlying R C D E S T U).map x y ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonOriginalComponents R C E S U
        (quotientEpsilonHorizontalObject R C D E S T U x)
        (quotientEpsilonHorizontalObject R C D E S T U y) =
    quotientEpsilonHorizontalExtension R C D E S T U x y ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonExtendedComponents R C E S U
        (quotientEpsilonHorizontalObject R C D E S T U x)
        (quotientEpsilonHorizontalObject R C D E S T U y) := by
  apply Pi.hom_ext
  intro c
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonOriginalComponents_π,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonExtendedComponents_π, quotientEpsilonHorizontalExtension,
    dgFunctorHomTransport_π, dgFunctorHorizontal_π_assoc]
  change ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T x.1 y.1 ⊗ₘ
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R D E T U x.2 y.2) ≫
    dgFunctorHorizontal R C D E x.1.val y.1.val x.2.val y.2.val) ≫
    dgFunctorHomπ R C E _ _ c ≫ (DGQuotient.inclusion R E U).map _ _ = _
  simp only [dgFunctorHomπ, Category.assoc]
  rw [dgFunctorHorizontal_π_assoc]
  dsimp only [DGFunctor.comp, EnrichedFunctor.comp]
  rw [(DGQuotient.inclusion R E U).map_comp]
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension_π_assoc,
    eqToHom_refl, Category.comp_id]
  rw [← DGQuotient.quotientDGFunctor_original R D E x.2.val T U x.2.property]
  erw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension_π R D E T U x.2 y.2 (y.1.val.obj c)]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
