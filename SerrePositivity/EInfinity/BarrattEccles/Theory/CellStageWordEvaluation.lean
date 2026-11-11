module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageActionWeights
public import SerrePositivity.EInfinity.BarrattEccles.Theory.FreeWordEvaluation
public import SerrePositivity.EInfinity.BarrattEccles.Theory.OperadWordEvaluation

/-!
# 実際のセル段の基底語と生成元の像での評価

## 概要
Berger–Moerdijk 命題 4.1 の自由表示で、セル段の基底語を演算として評価する。

## 方針
自由表示の逆同型で自由生成元を移し、Schur 生成射を生成元への作用で表す。

## 規約
生成元の像は元のセル段の各次数の元として定義する。

## 使われ方
付加生成元の微分の評価から、セル段の各基底語の微分を評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits HomologicalComplex HomotopicalAlgebra DifferentialGraded TensorPowers
attribute [local implicit_reducible] operad Operad.cellStageGeneratorSpheres
variable {A : Type u} [CommRing A]
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : (operad A).Algebra} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u}
    (fun (_ : J) n => (operad A).freeAlgebraFunctor.map (complexSphereToDisk A n)) f)

/-- The image in the actual stage of one homogeneous generator of its free presentation. -/
def cellStageGeneratorValue (hX : IsInitial X) (j : J) (i : ℤ)
    (x : (cellStageGeneratorWeightBasis c hX j).index i) : (c.F.obj j).carrier.X i :=
  (Operad.cellStageSchurDegreeIso c hX j i).inv
    (((operad A).schurUnit (∐ (Operad.cellStageGeneratorSpheres c j))).f i
      ((cellStageGeneratorWeightBasis c hX j).basis i x))

/-- A normalized actual cell basis word is its coefficient operation on these generator images. -/
lemma cellStageWordBasis_evaluated (hX : IsInitial X) (j : J) (i : ℤ) (n q : ℕ)
    (a : ULift.{u} (BasedNondegenerate n q))
    (v : powerGradedIndex (cellStageGeneratorWeightBasis c hX j).index n (i + q)) :
    cellStageWordBasis c hX j i (schurNonpositiveWordIndex i n q (a, v)) =
      Operad.evaluatedWord (c.F.obj j) (cellStageGeneratorValue c hX j)
        (-(q : ℤ)) (i + q) i (by omega) n (equivariantBasis A n q (a, 1)) v := by
  let K := ∐ (Operad.cellStageGeneratorSpheres c j)
  let b := (cellStageGeneratorWeightBasis c hX j).basis
  let g := fun i z => ((operad A).schurUnit K).f i (b i z)
  have hf := Operad.schurGenerator_eq_actionValue (operad A) b n
    (-(q : ℤ)) (i + q) i (by omega) (equivariantBasis A n q (a, 1)) v
  have he := Operad.erasedIso_action_value (Operad.cellStageErasedFreeIso c hX j).symm
    g n (-(q : ℤ)) (i + q) i (by omega) (equivariantBasis A n q (a, 1)) v
  rw [cellStageWordBasis, Module.Basis.map_apply, schurWordBasis_nonpositive]
  erw [hf]
  exact he

end SerrePositivity.EInfinity.BarrattEccles
