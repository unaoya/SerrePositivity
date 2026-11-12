module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseEndpoints
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：twisted arrow 単体集合と、その始点・終点を記録する実際の射影。
方針：既存の edgewise subdivision の左右の射影を直積へ束ねる。
規約：この構成は任意の単体集合に定義し、left fibration 性は別に証明する。
使われ方：空間値 Hom 関手と Yoneda 関手の入力となる射影。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- twisted arrow の n 単体は Δ[n]op ⋆ Δ[n] からの射。 -/
@[kerodon 03JG]
abbrev TwistedArrow (C : SSet.{u}) : SSet.{u} := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision C

/-- twisted arrow の始点と終点を同時に記録する射影。 -/
@[kerodon 03JK]
def twistedArrowProjection (C : SSet.{u}) : TwistedArrow C ⟶ C.op ⊗ C :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C)

/-- 第一成分は始点を反転した底に記録する。 -/
lemma twistedArrowProjection_fst (C : SSet.{u}) :
    twistedArrowProjection C ≫ fst C.op C = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C :=
  lift_fst _ _

/-- 第二成分は終点を元の底に記録する。 -/
lemma twistedArrowProjection_snd (C : SSet.{u}) :
    twistedArrowProjection C ≫ snd C.op C = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C :=
  lift_snd _ _

/-- 射影は底の射について厳密に自然。 -/
lemma twistedArrowProjection_naturality {C D : SSet.{u}} (f : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f ≫ twistedArrowProjection D =
      twistedArrowProjection C ≫ (SSet.opFunctor.map f ⊗ₘ f) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro g
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
