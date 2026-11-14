module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SmallShapeColimits
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamilies
import all SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamilies
import all SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamily
import all SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.RelativeInitialVertices

/-!
# strict 半自由図式の native な普遍余錐の全関手族

## 概要
strict 図式圏の全 nerve をパラメーターとして、同じ下方図式を持つ native な普遍余錐の族を作る。

## 方針
全評価を curry し、普遍余錐の全部分圏の射影の trivial Kan fibration を切断する。

## 規約
存在の入力には既存の bar を使う。実現複体との計算比較はこの選択だけから主張しない。

## 使われ方
HTT 4.2.4.1、HA 1.2.4。Δᵒᵖ の指定余錐と図式の射・高次単体の同時構成。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 添字を固定し、strict 半自由図式の全パラメーターを動かす図式の族。 -/
def strictSemifreeDiagramFamily :
    nerve (StrictSemifreeDiagram A J) ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve J))).obj
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) :=
  curry ((β_ ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve J))
    (nerve (StrictSemifreeDiagram A J))).hom ≫ strictSemifreeEvaluation A J)

/-- 元の全図式族へ厳密に射影する、native な普遍余錐の全関手族。 -/
def strictSemifreeColimitFamily :
    nerve (StrictSemifreeDiagram A J) ⟶
      colimitCocones ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve J))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) :=
  (exists_colimitCoconeFamily (strictSemifreeDiagramFamily A J)
    (fun a => smallShape_hasColimit A (nerve J)
      ((functorVertexEquiv _ _).symm
        ((strictSemifreeDiagramFamily A J).app (Opposite.op ⦋0⦌) a)))).choose

/-- 普遍余錐の族の下方図式は、全高次単体で元の同じ評価の族と一致する。 -/
theorem strictSemifreeColimitFamily_projection :
    strictSemifreeColimitFamily A J ≫
      colimitCoconeProjection ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve J))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) = strictSemifreeDiagramFamily A J :=
  (exists_colimitCoconeFamily (strictSemifreeDiagramFamily A J)
    (fun a => smallShape_hasColimit A (nerve J)
      ((functorVertexEquiv _ _).symm
        ((strictSemifreeDiagramFamily A J).app (Opposite.op ⦋0⦌) a)))).choose_spec

/-- 普遍余錐の族を全余錐の関手単体集合へ含めた全写像。 -/
def strictSemifreeCoconeFunctorFamily :
    nerve (StrictSemifreeDiagram A J) ⟶
      (ihom (join ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve J)) (Δ[0] : SSet.{u + 1}))).obj
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) :=
  strictSemifreeColimitFamily A J ≫
    (relativeInitialVertices (coconeRestriction
      ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve J)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).ι

/-- 全余錐の族への包含後も、下方図式は同じ全評価の族と厳密に一致する。 -/
theorem strictSemifreeCoconeFunctorFamily_restriction :
    strictSemifreeCoconeFunctorFamily A J ≫
      coconeRestriction ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve J))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) = strictSemifreeDiagramFamily A J := by
  change strictSemifreeColimitFamily A J ≫
    ((relativeInitialVertices (coconeRestriction
      ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve J)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).ι ≫
      coconeRestriction ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve J))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)) = _
  exact strictSemifreeColimitFamily_projection A J

/-- 全パラメーターと join の全単体を同時に評価する native な余錐の族。 -/
def strictSemifreeJoinCoconeFamily :
    nerve (StrictSemifreeDiagram A J) ⊗
      join ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve J)) (Δ[0] : SSet.{u + 1}) ⟶
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A :=
  (β_ _ _).hom ≫ uncurry (strictSemifreeCoconeFunctorFamily A J)

/-- 同じ join 余錐の族の apex を評価する全関手。実現複体との比較は別に行う。 -/
def strictSemifreeNativeApexFamily :
    nerve (StrictSemifreeDiagram A J) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A :=
  lift (𝟙 _) (SSet.stdSimplex.isTerminalObj₀.from _) ≫
    (nerve (StrictSemifreeDiagram A J) ◁
      joinInr ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve J)) Δ[0]) ≫
      strictSemifreeJoinCoconeFamily A J

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
