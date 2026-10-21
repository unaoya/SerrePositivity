module

public import SerrePositivity.InfinityCategories.F1.EquivalenceTriangle
public import SerrePositivity.InfinityCategories.F1B.FunctorHomEvaluation

/-!
概要：元の可逆三角形の頂点評価と定値三角形の切断。
方針：元の関手空間の評価と定値関手を全部分複体へ制限する。
規約：三角形の全高次パラメーターを保持する。
使われ方：元の三角形の各面の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の可逆三角形の指定した頂点での評価。 -/
def equivalenceTriangleEvaluation (Y : SSet.{u}) (i : Fin 3) : equivalenceTriangle Y ⟶ Y :=
  equivalenceTriangleι Y ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i)

/-- 同じ定値三角形の三辺は全て可逆。 -/
lemma isEquivalenceTriangleVertex_constant {Y : SSet.{u}} (y : Y _⦋0⦌) :
    IsEquivalenceTriangleVertex ((constantFunctorMap (Δ[2] : SSet.{u}) Y).app _ y) := by
  rw [constantFunctorMap_vertex]
  intro i
  rw [triangleFunctorVertexSimplex_functorVertex]
  rw [← stdSimplex.yonedaEquiv_δ_comp]
  change IsInvertibleEdge (edgeOfSimplex (PinchedHom.constant y 1))
  exact (isInvertibleEdge_congr (pinchedConstant_one y)).mpr
    (show IsInvertibleEdge (SSet.Truncated.Edge.id (X := (truncation 2).obj Y) y) from
      by
        change IsIso (SSet.Truncated.HomotopyCategory.homMk _)
        rw [SSet.Truncated.HomotopyCategory.homMk_id]
        infer_instance)

/-- 同じ定値三角形を元の可逆三角形の空間へ含める。 -/
def equivalenceTriangleConstant (Y : SSet.{u}) : Y ⟶ equivalenceTriangle Y :=
  fullSubcomplexLift _ (constantFunctorMap (Δ[2] : SSet.{u}) Y)
    isEquivalenceTriangleVertex_constant

/-- 定値三角形の包含は、元の同じ定値関手の族。 -/
lemma equivalenceTriangleConstant_ι (Y : SSet.{u}) :
    equivalenceTriangleConstant Y ≫ equivalenceTriangleι Y =
      constantFunctorMap (Δ[2] : SSet.{u}) Y := fullSubcomplexLift_ι _ _ _

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
    equivalenceTriangleEvaluation Y 0 ≫ constantFunctorMap (Δ[2] : SSet.{u}) Y =
      equivalenceTriangleι Y ≫ (pre (SSet.const
        (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) : (Δ[2] : SSet.{u}) ⟶ Δ[2])).app Y := by
  rw [equivalenceTriangleEvaluation, Category.assoc, evaluateFunctorAt_constantFunctorMap]

end SerrePositivity.InfinityCategories
