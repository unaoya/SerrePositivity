module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangle
public import SerrePositivity.InfinityCategories.F1.QuasicategoryDiagramRealizationVertices
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeJointComparisonEvaluation

/-!
概要：元の底変換比較の三辺を持つ豊穣三角形を、全 fibration の coherent な族へ実現する。
方針：同じ三点図式を共同実現し、定値パラメーターの二単体を厳密に回収する。
規約：元の全高次 Hom と同じ比較の三辺を保持する。
使われ方：Hom 比較 span の合成と二次元 Segal 制限の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 元の三辺を持つ同じ三角形の、全 fibration・全高次 Hom の共同実現。 -/
def cocartesianBaseChangeTriangleFamily :
    CocartesianFibrationInfinity (nerve C) ⟶
      CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Fin 3 × A))) :=
  (cocartesianBaseChangeTriangle l k).realization

/-- 一つの元の fibration に固定すると、同じ元の三角形図式全体を回収する。 -/
lemma cocartesianBaseChangeTriangleFamily_vertex (p : CocartesianFibrationCategory (nerve C)) :
    (cocartesianBaseChangeTriangleFamily l k).app (Opposite.op ⦋0⦌) (coherentNerveVertex p) =
      functorVertex (qCatDiagramCoherentNerve (quasicategoryDiagramValueFunctor
        ((cocartesianBaseChangeTriangle l k).toCoreEnrichedFunctor.obj p))) :=
  (cocartesianBaseChangeTriangle l k).realization_vertex p

/-- 同じ共同実現を一つの底対象と元の fibration に固定した、実際の二単体。 -/
def cocartesianBaseChangeTriangleSimplex (p : CocartesianFibrationCategory (nerve C)) (a : A) :
    CatInfinity.{u} _⦋2⦌ :=
  (((cocartesianBaseChangeTriangleFamily l k).app (Opposite.op ⦋2⦌)
    (PinchedHom.constant (coherentNerveVertex p) 2)).app (Opposite.op ⦋2⦌)
      (𝟙 (Opposite.op ⦋2⦌))) (ULift.up (ComposableArrows.mk₂
        ((homOfLE (show (0 : Fin 3) ≤ 1 by decide), 𝟙 a) :
          ((0 : Fin 3), a) ⟶ ((1 : Fin 3), a))
        ((homOfLE (show (1 : Fin 3) ≤ 2 by decide), 𝟙 a) :
          ((1 : Fin 3), a) ⟶ ((2 : Fin 3), a))))

/-- 同じ二単体は、元の三角形の同じ二射の列を coherent に写したもの。 -/
lemma cocartesianBaseChangeTriangleSimplex_eq
    (p : CocartesianFibrationCategory (nerve C)) (a : A) :
    cocartesianBaseChangeTriangleSimplex l k p a =
      (qCatDiagramCoherentNerve (quasicategoryDiagramValueFunctor
        ((cocartesianBaseChangeTriangle l k).toCoreEnrichedFunctor.obj p))).app
          (Opposite.op ⦋2⦌) (ULift.up (ComposableArrows.mk₂
            ((homOfLE (show (0 : Fin 3) ≤ 1 by decide), 𝟙 a) :
              ((0 : Fin 3), a) ⟶ ((1 : Fin 3), a))
            ((homOfLE (show (1 : Fin 3) ≤ 2 by decide), 𝟙 a) :
              ((1 : Fin 3), a) ⟶ ((2 : Fin 3), a)))) := by
  change quasicategoryDiagramDiagonalSimplex
    (ComposableArrows.mk₂
      ((homOfLE (show (0 : Fin 3) ≤ 1 by decide), 𝟙 a) :
        ((0 : Fin 3), a) ⟶ ((1 : Fin 3), a))
      ((homOfLE (show (1 : Fin 3) ≤ 2 by decide), 𝟙 a) :
        ((1 : Fin 3), a) ⟶ ((2 : Fin 3), a)))
    ((coherentNerveMap (cocartesianBaseChangeTriangle l k).toCoreEnrichedFunctor).app
      (Opposite.op ⦋2⦌) (PinchedHom.constant (coherentNerveVertex p) 2)) = _
  rw [pinchedConstant_map, coherentNerveMap_vertex,
    quasicategoryDiagramDiagonalSimplex_constant]

end SerrePositivity.InfinityCategories
