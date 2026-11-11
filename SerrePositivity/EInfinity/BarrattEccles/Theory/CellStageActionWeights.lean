module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageWeights
public import SerrePositivity.EInfinity.BarrattEccles.Theory.ErasedIsoWeightTransfer
public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurActionWeights

/-!
# 実際のセル段の演算と語の重み

## 概要
Berger–Moerdijk 命題 4.1 のセル段で、演算が元の生成元の総重みを増やさない。

## 方針
微分を消した自由表示の同型と、指定された語の基底を比較する。

## 規約
元のセル段の微分を消すのは比較の同型を作るときだけ。

## 使われ方
セル段の微分の重み評価と K 平坦性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits MonoidalCategory HomologicalComplex HomotopicalAlgebra
open DifferentialGraded TensorPowers ComplexWeightBasis
open scoped TensorProduct
variable {A : Type u} [CommRing A]
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : (operad A).Algebra} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u}
    (fun (_ : J) n => (operad A).freeAlgebraFunctor.map (complexSphereToDisk A n)) f)

/-- The weighted basis of the original generator spheres of a stage. -/
abbrev cellStageGeneratorWeightBasis (hX : IsInitial X) (j : J) :
    ComplexWeightBasis (∐ (Operad.cellStageGeneratorSpheres c j)) :=
  ⟨SphereCoproductIndex (fun x : CellsBefore (Operad.CellsAt c) j =>
      Operad.cellDegree c x.1 x.2),
    sphereCoproductDegreeBasis (fun x : CellsBefore (Operad.CellsAt c) j =>
      Operad.cellDegree c x.1 x.2), cellStageInputWeight c hX j⟩

/-- The weighted basis on the original carrier of a stage. -/
abbrev cellStageWeightBasis (hX : IsInitial X) (j : J) :
    ComplexWeightBasis ((c.F.obj j).carrier) :=
  ⟨SchurWordIndex (cellStageGeneratorWeightBasis c hX j).index,
    cellStageWordBasis c hX j, fun x => cellStageBasisWeight c hX j x.1 x.2⟩

/-- The degree comparison identifies each actual basis vector with its free Schur word. -/
lemma cellStageWordBasis_compare (hX : IsInitial X) (j : J) (i : ℤ)
    (x : SchurWordIndex (cellStageGeneratorWeightBasis c hX j).index i) :
    (Operad.cellStageErasedFreeIso c hX j).hom.hom.f i (cellStageWordBasis c hX j i x) =
      schurWordBasis (cellStageGeneratorWeightBasis c hX j).basis i x := by
  rw [cellStageWordBasis, Module.Basis.map_apply]
  exact (Operad.cellStageSchurDegreeIso c hX j i).toLinearEquiv.apply_symm_apply _

/-- The original action at a cell stage preserves the total original generator weight. -/
lemma cellStageAction_mem_basisWeightSpan (hX : IsInitial X) (j : J)
    (n : ℕ) (p r i : ℤ) (h : p + r = i) (u : ((operad A).arity n).X p)
    (N : ℕ) {v : (power (c.F.obj j).carrier n).X r}
    (hv : v ∈ basisWeightSpan (powerGradedBasis (cellStageWordBasis c hX j) n r)
      (powerGradedWeight (cellStageWeightBasis c hX j).weight n r) N) :
    ((c.F.obj j).action n).f i
      (ιTensorObj ((operad A).arity n) (power (c.F.obj j).carrier n) p r i h (u ⊗ₜ[A] v)) ∈
      basisWeightSpan (cellStageWordBasis c hX j i) (cellStageBasisWeight c hX j i) N := by
  exact Operad.action_weightBound_of_erasedIso
    (Operad.cellStageErasedFreeIso c hX j) (cellStageWordBasis c hX j)
    (schurWordBasis (cellStageGeneratorWeightBasis c hX j).basis)
    (cellStageWordBasis_compare c hX j) (cellStageWeightBasis c hX j).weight
    (fun n p r i h u N _ hv => schurAction_mem_basisWeightSpan
      (cellStageGeneratorWeightBasis c hX j) n p r i h u N hv) n p r i h u N hv

end SerrePositivity.EInfinity.BarrattEccles
