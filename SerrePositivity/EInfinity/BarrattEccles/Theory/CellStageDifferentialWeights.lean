module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageWordEvaluation
public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurUnitWeights

/-!
# 実際のセル段の語の微分と生成元の微分

## 概要
Berger–Moerdijk 命題 4.1 のセル段で、語の微分の重みを生成元の微分へ帰着する。

## 方針
指定生成元の像の重みを自由表示で評価し、演算の語の Leibniz 則を使う。

## 規約
この帰着には生成元の微分の重みの上限を明示的に仮定する。

## 使われ方
実際の付加の境界の照合を、セル段の K 平坦性へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits HomologicalComplex HomotopicalAlgebra DifferentialGraded
open SerrePositivity.InfinityCategories
attribute [local implicit_reducible] operad Operad.cellStageGeneratorSpheres
attribute [local irreducible] Operad.cellStageSchurDegreeIso
variable {A : Type u} [CommRing A]
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : (operad A).Algebra} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u}
    (fun (_ : J) n => (operad A).freeAlgebraFunctor.map (complexSphereToDisk A n)) f)

/-- The image of each free generator has at most its globally assigned cell weight. -/
lemma cellStageGeneratorValue_mem (hX : IsInitial X) (j : J) (i : ℤ)
    (z : (cellStageGeneratorWeightBasis c hX j).index i) :
    cellStageGeneratorValue c hX j i z ∈
      basisWeightSpan (cellStageWordBasis c hX j i) (cellStageBasisWeight c hX j i)
        ((cellStageGeneratorWeightBasis c hX j).weight ⟨i, z⟩) := by
  let b := cellStageGeneratorWeightBasis c hX j
  let e := Operad.cellStageSchurDegreeIso c hX j i
  have he : ∀ x, e.toLinearEquiv (cellStageWordBasis c hX j i x) =
      schurWordBasis b.basis i x := by
    intro x
    rw [cellStageWordBasis, Module.Basis.map_apply]
    exact e.toLinearEquiv.apply_symm_apply _
  apply (mem_basisWeightSpan_iff_map (cellStageWordBasis c hX j i)
    (schurWordBasis b.basis i) e.toLinearEquiv he
    (cellStageBasisWeight c hX j i) _ _).mpr
  change (e.inv ≫ e.hom)
    (((operad A).schurUnit (∐ (Operad.cellStageGeneratorSpheres c j))).f i (b.basis i z)) ∈ _
  rw [e.inv_hom_id]
  exact preserves_schurUnit b i _
    (basis_mem_basisWeightSpan (b.basis i) (fun z => b.weight ⟨i, z⟩) z)

/-- Bounding the actual generator differentials bounds the differential of every basis word. -/
lemma cellStageWordBasis_d_mem_of_generator (hX : IsInitial X) (j : J)
    (hdg : ∀ i z, (c.F.obj j).carrier.d i (i + 1) (cellStageGeneratorValue c hX j i z) ∈
      basisWeightSpan (cellStageWordBasis c hX j (i + 1))
        (cellStageBasisWeight c hX j (i + 1))
        ((cellStageGeneratorWeightBasis c hX j).weight ⟨i, z⟩))
    (i : ℤ) (x : (cellStageWeightBasis c hX j).index i) :
    (c.F.obj j).carrier.d i (i + 1) (cellStageWordBasis c hX j i x) ∈
      basisWeightSpan (cellStageWordBasis c hX j (i + 1))
        (cellStageBasisWeight c hX j (i + 1)) (cellStageBasisWeight c hX j i x) := by
  obtain ⟨n, q, a, v, rfl⟩ := schurWordIndex_exists_nonpositive i x
  rw [cellStageWordBasis_evaluated, cellStageBasisWeight, schurWordWeight_nonpositive]
  exact Operad.evaluatedWord_d_mem (c.F.obj j) (cellStageWordBasis c hX j)
    (cellStageWeightBasis c hX j).weight (cellStageGeneratorValue c hX j)
    (cellStageGeneratorWeightBasis c hX j).weight (cellStageGeneratorValue_mem c hX j)
    (fun p r i h n u N _ hv => cellStageAction_mem_basisWeightSpan c hX j n p r i h u N hv)
    hdg (-(q : ℤ)) (i + q) i (by omega) n (equivariantBasis A n q (a, 1)) v

/-- The actual stage is K-flat once the actual free generator differentials have their bounds. -/
lemma cellStageKFlat_of_generator_d (hX : IsInitial X) (j : J)
    (hdg : ∀ i z, (c.F.obj j).carrier.d i (i + 1) (cellStageGeneratorValue c hX j i z) ∈
      basisWeightSpan (cellStageWordBasis c hX j (i + 1))
        (cellStageBasisWeight c hX j (i + 1))
        ((cellStageGeneratorWeightBasis c hX j).weight ⟨i, z⟩)) :
    complexKFlat A (c.F.obj j).carrier := by
  apply complexKFlat_of_weightedBasis (cellStageWordBasis c hX j)
    (cellStageBasisWeight c hX j) (cellStageBasisDegree_le_weight c hX j)
  intro i x y hy
  exact (mem_basisWeightSpan (cellStageWordBasis c hX j (i + 1))
    (cellStageBasisWeight c hX j (i + 1)) _ _).mp
      (cellStageWordBasis_d_mem_of_generator c hX j hdg i x) y hy

end SerrePositivity.EInfinity.BarrattEccles
