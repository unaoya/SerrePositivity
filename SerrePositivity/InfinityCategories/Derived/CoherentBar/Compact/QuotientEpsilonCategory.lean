module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonHom
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (S : Set C) (T : Set D)
local instance : HasProductsOfShape C (ModuleCat.{u} R) := ModuleCat.hasLimitsOfShape

/-- 元の同じ単位と、固定商関手の同じ単位の同時持ち上げ。 -/
def quotientEpsilonIdentity (F : NullPreservingFunctorsε R C D S T) :
    𝟙_ (Complex R) ⟶ quotientEpsilonHom R C D S T F F :=
  pullback.lift (dgFunctorIdentity R C D F.val)
    (dgFunctorIdentity R _ _ (quotientEpsilonObject R C D S T F)) (by
      apply Pi.hom_ext
      intro x
      simp only [Category.assoc, quotientEpsilonOriginalComponents_π,
        quotientEpsilonExtendedComponents_π, dgFunctorIdentity_π,
        dgFunctorIdentity_π_assoc]
      exact (DGQuotient.inclusion R D T).map_id (F.val.obj x))

@[reassoc (attr := simp)]
lemma quotientEpsilonIdentity_ι (F : NullPreservingFunctorsε R C D S T) :
    quotientEpsilonIdentity R C D S T F ≫ quotientEpsilonHomι R C D S T F F =
      dgFunctorIdentity R C D F.val := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma quotientEpsilonIdentity_extension (F : NullPreservingFunctorsε R C D S T) :
    quotientEpsilonIdentity R C D S T F ≫ quotientEpsilonHomExtension R C D S T F F =
      dgFunctorIdentity R _ _ (quotientEpsilonObject R C D S T F) :=
  pullback.lift_snd _ _ _

/-- 同じ tensor パラメータを持つ元の縦合成と商上の縦合成を同時に持ち上げる。 -/
def quotientEpsilonComposition (F G H : NullPreservingFunctorsε R C D S T) :
    quotientEpsilonHom R C D S T F G ⊗ quotientEpsilonHom R C D S T G H ⟶
      quotientEpsilonHom R C D S T F H :=
  pullback.lift
    ((quotientEpsilonHomι R C D S T F G ⊗ₘ quotientEpsilonHomι R C D S T G H) ≫
      dgFunctorComposition R C D F.val G.val H.val)
    ((quotientEpsilonHomExtension R C D S T F G ⊗ₘ
      quotientEpsilonHomExtension R C D S T G H) ≫
      dgFunctorComposition R _ _ (quotientEpsilonObject R C D S T F)
        (quotientEpsilonObject R C D S T G) (quotientEpsilonObject R C D S T H)) (by
      apply Pi.hom_ext
      intro x
      simp only [Category.assoc, quotientEpsilonOriginalComponents_π,
        quotientEpsilonExtendedComponents_π, dgFunctorComposition_π,
        dgFunctorComposition_π_assoc]
      rw [← Category.assoc, (DGQuotient.inclusion R D T).map_comp]
      simp only [Category.assoc, tensorHom_comp_tensorHom_assoc,
        quotientEpsilonHomExtension_π]
      rfl)

@[reassoc (attr := simp)]
lemma quotientEpsilonComposition_ι (F G H : NullPreservingFunctorsε R C D S T) :
    quotientEpsilonComposition R C D S T F G H ≫ quotientEpsilonHomι R C D S T F H =
      (quotientEpsilonHomι R C D S T F G ⊗ₘ quotientEpsilonHomι R C D S T G H) ≫
        dgFunctorComposition R C D F.val G.val H.val := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma quotientEpsilonComposition_extension (F G H : NullPreservingFunctorsε R C D S T) :
    quotientEpsilonComposition R C D S T F G H ≫
        quotientEpsilonHomExtension R C D S T F H =
      (quotientEpsilonHomExtension R C D S T F G ⊗ₘ
        quotientEpsilonHomExtension R C D S T G H) ≫
        dgFunctorComposition R _ _ (quotientEpsilonObject R C D S T F)
          (quotientEpsilonObject R C D S T G) (quotientEpsilonObject R C D S T H) :=
  pullback.lift_snd _ _ _

/-- 同じ対象と固定 ε 整合 Hom を持つ dg 関手圏。 -/
instance nullPreservingFunctorsεEnrichment : DGCategory R (NullPreservingFunctorsε R C D S T) := by
  letI := inducedDGCategory R (fun F : NullPreservingFunctorsε R C D S T => F.val)
  exact dgCategoryOfFaithfulHomMaps R (NullPreservingFunctorsε R C D S T)
    (quotientEpsilonHom R C D S T) (quotientEpsilonHomι R C D S T)
    (quotientEpsilonIdentity R C D S T) (quotientEpsilonComposition R C D S T)
    (quotientEpsilonIdentity_ι R C D S T) (quotientEpsilonComposition_ι R C D S T)

/-- 元の全次数 Hom への部分複体包含を束ねた忘却 dg 関手。 -/
def nullPreservingFunctorsεForget :
    DGFunctor R (NullPreservingFunctorsε R C D S T) (DGFunctor R C D) where
  obj F := F.val
  map := quotientEpsilonHomι R C D S T
  map_id := quotientEpsilonIdentity_ι R C D S T
  map_comp := quotientEpsilonComposition_ι R C D S T

/-- 固定 ε 整合 Hom の圏から、同じ正本商関手圏への全次数豊穣作用。 -/
def quotientInputFunctor :
    DGFunctor R (NullPreservingFunctorsε R C D S T)
      (DGFunctor R (DGQuotient.QuotientObject C S) (DGQuotient.QuotientObject D T)) where
  obj := quotientEpsilonObject R C D S T
  map := quotientEpsilonHomExtension R C D S T
  map_id := quotientEpsilonIdentity_extension R C D S T
  map_comp := quotientEpsilonComposition_extension R C D S T

/-- 対象作用は選び直さず、既存の同じ固定 ε を持つ正本商関手そのもの。 -/
lemma quotientInputFunctor_obj (F : NullPreservingFunctorsε R C D S T) :
    (quotientInputFunctor R C D S T).obj F =
      DGQuotient.quotientDGFunctor R C D F.val S T F.property := rfl

end SerrePositivity.InfinityCategories
