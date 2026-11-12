module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonHom
public import SerrePositivity.DifferentialGraded.Category.Tensor

/-!
概要：固定 ε 整合 Hom 部分複体で dg 関手圏を作り、同じ正本商への豊穣作用を供給する。
方針：元の単位・縦合成と商上の単位・縦合成を pullback へ同時に持ち上げる。
規約：一般の null 保存関手圏の全 Hom からの作用は主張しない。
使われ方：D-S が ε 整合な resolved 作用を着地させる正本型。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory Limits MonoidalCategory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (S : Set C) (T : Set D)
local instance : HasProductsOfShape C (ModuleCat.{u} R) := ModuleCat.hasLimitsOfShape

/-- 元の同じ単位と、固定商関手の同じ単位の同時持ち上げ。 -/
def quotientEpsilonIdentity (F : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) :
    𝟙_ (Complex R) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C D S T F F :=
  pullback.lift (dgFunctorIdentity R C D F.val)
    (dgFunctorIdentity R _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T F)) (by
      apply Pi.hom_ext
      intro x
      simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonOriginalComponents_π,
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonExtendedComponents_π, dgFunctorIdentity_π,
        dgFunctorIdentity_π_assoc]
      exact (DGQuotient.inclusion R D T).map_id (F.val.obj x))

@[reassoc (attr := simp)]
lemma quotientEpsilonIdentity_ι (F : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) :
    quotientEpsilonIdentity R C D S T F ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T F F =
      dgFunctorIdentity R C D F.val := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma quotientEpsilonIdentity_extension (F : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) :
    quotientEpsilonIdentity R C D S T F ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension R C D S T F F =
      dgFunctorIdentity R _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T F) :=
  pullback.lift_snd _ _ _

/-- 同じ tensor パラメータを持つ元の縦合成と商上の縦合成を同時に持ち上げる。 -/
def quotientEpsilonComposition (F G H : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C D S T F G ⊗ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C D S T G H ⟶
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C D S T F H :=
  pullback.lift
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T F G ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T G H) ≫
      dgFunctorComposition R C D F.val G.val H.val)
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension R C D S T F G ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension R C D S T G H) ≫
      dgFunctorComposition R _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T F)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T G) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T H)) (by
      apply Pi.hom_ext
      intro x
      simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonOriginalComponents_π,
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonExtendedComponents_π, dgFunctorComposition_π,
        dgFunctorComposition_π_assoc]
      rw [← Category.assoc, (DGQuotient.inclusion R D T).map_comp]
      simp only [Category.assoc, tensorHom_comp_tensorHom_assoc,
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension_π]
      rfl)

@[reassoc (attr := simp)]
lemma quotientEpsilonComposition_ι (F G H : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) :
    quotientEpsilonComposition R C D S T F G H ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T F H =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T F G ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T G H) ≫
        dgFunctorComposition R C D F.val G.val H.val := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma quotientEpsilonComposition_extension (F G H : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) :
    quotientEpsilonComposition R C D S T F G H ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension R C D S T F H =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension R C D S T F G ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension R C D S T G H) ≫
        dgFunctorComposition R _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T F)
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T G) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T H) :=
  pullback.lift_snd _ _ _

/-- 同じ対象と固定 ε 整合 Hom を持つ dg 関手圏。 -/
instance nullPreservingFunctorsεEnrichment : DGCategory R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) := by
  letI := inducedDGCategory R (fun F : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T => F.val)
  exact dgCategoryOfFaithfulHomMaps R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C D S T) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T)
    (quotientEpsilonIdentity R C D S T) (quotientEpsilonComposition R C D S T)
    (quotientEpsilonIdentity_ι R C D S T) (quotientEpsilonComposition_ι R C D S T)

/-- 元の全次数 Hom への部分複体包含を束ねた忘却 dg 関手。 -/
def nullPreservingFunctorsεForget :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) (DGFunctor R C D) where
  obj F := F.val
  map := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T
  map_id := quotientEpsilonIdentity_ι R C D S T
  map_comp := quotientEpsilonComposition_ι R C D S T

/-- 固定 ε 整合 Hom の圏から、同じ正本商関手圏への全次数豊穣作用。 -/
def quotientInputFunctor :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T)
      (DGFunctor R (DGQuotient.QuotientObject C S) (DGQuotient.QuotientObject D T)) where
  obj := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T
  map := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension R C D S T
  map_id := quotientEpsilonIdentity_extension R C D S T
  map_comp := quotientEpsilonComposition_extension R C D S T

/-- 対象作用は選び直さず、既存の同じ固定 ε を持つ正本商関手そのもの。 -/
lemma quotientInputFunctor_obj (F : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) :
    (quotientInputFunctor R C D S T).obj F =
      DGQuotient.quotientDGFunctor R C D F.val S T F.property := rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
