module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceTriangle
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation

/-!
概要：元の可逆三角形の頂点評価と定値三角形の切断。
方針：元の関手空間の評価と定値関手を全部分複体へ制限する。
規約：三角形の全高次パラメーターを保持する。
使われ方：元の三角形の各面の同値性。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 元の可逆三角形の指定した頂点での評価。 -/
def equivalenceTriangleEvaluation (Y : SSet.{u}) (i : Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangle Y ⟶ Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangleι Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i)

/-- 同じ定値三角形の三辺は全て可逆。 -/
lemma isEquivalenceTriangleVertex_constant {Y : SSet.{u}} (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalenceTriangleVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[2] : SSet.{u}) Y).app _ y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex]
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.triangleFunctorVertexSimplex_functorVertex]
  rw [← stdSimplex.yonedaEquiv_δ_comp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 1))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one y)).mpr
    (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (SSet.Truncated.Edge.id (X := (truncation 2).obj Y) y) from
      by
        change IsIso (SSet.Truncated.HomotopyCategory.homMk _)
        rw [SSet.Truncated.HomotopyCategory.homMk_id]
        infer_instance)

/-- 同じ定値三角形を元の可逆三角形の空間へ含める。 -/
def equivalenceTriangleConstant (Y : SSet.{u}) : Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangle Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[2] : SSet.{u}) Y)
    isEquivalenceTriangleVertex_constant

/-- 定値三角形の包含は、元の同じ定値関手の族。 -/
lemma equivalenceTriangleConstant_ι (Y : SSet.{u}) :
    equivalenceTriangleConstant Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangleι Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[2] : SSet.{u}) Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 定値三角形の各頂点の評価は、元の恒等写像。 -/
lemma equivalenceTriangleConstant_evaluation (Y : SSet.{u}) (i : Fin 3) :
    equivalenceTriangleConstant Y ≫ equivalenceTriangleEvaluation Y i = 𝟙 Y := by
  rw [equivalenceTriangleEvaluation, ← Category.assoc, equivalenceTriangleConstant_ι]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro y
  change Y.map (𝟙 (Opposite.op ⦋n⦌)) y = y
  exact CategoryTheory.Functor.map_id_apply Y _ y

/-- 初頂点で評価して定値三角形にする作用は、同じ定値写像による前合成。 -/
lemma equivalenceTriangleEvaluation_zero_constant (Y : SSet.{u}) :
    equivalenceTriangleEvaluation Y 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[2] : SSet.{u}) Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceTriangleι Y ≫ (pre (SSet.const
        (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) : (Δ[2] : SSet.{u}) ⟶ Δ[2])).app Y := by
  rw [equivalenceTriangleEvaluation, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.evaluateFunctorAt_constantFunctorMap]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
