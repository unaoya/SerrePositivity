module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageActionWeights
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageFreeNaturality
public import SerrePositivity.EInfinity.BarrattEccles.Theory.SphereCoproductInclusions
public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurMapWeights

/-!
# 実際のセル段の包含と語の重み

## 概要
Berger–Moerdijk 命題 4.1 のセル段の指定包含は、先行セルの語の総重みを増やさない。

## 方針
生成元の余積の基底を包含で比較し、Schur 関手と自由表示の自然性を使う。

## 規約
各セルの重みは全体で一度選んだものを使い、段が変わっても変えない。

## 使われ方
付加の実際の境界の重み評価を後の段へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits HomologicalComplex HomotopicalAlgebra DifferentialGraded
open ComplexWeightBasis
attribute [local implicit_reducible] cellsBeforeInclusion
variable {A : Type u} [CommRing A]
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : (operad A).Algebra} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u}
    (fun (_ : J) n => (operad A).freeAlgebraFunctor.map (complexSphereToDisk A n)) f)

/-- Generator coproduct inclusions carry each chosen basis vector to the same cell label. -/
lemma cellStageGeneratorCoproductMap_basis (hX : IsInitial X) {j k : J} (h : j ≤ k)
    (i : ℤ) (x : (cellStageGeneratorWeightBasis c hX j).index i) :
    (Operad.cellStageGeneratorCoproductMap c h).f i
      ((cellStageGeneratorWeightBasis c hX j).basis i x) =
      (cellStageGeneratorWeightBasis c hX k).basis i
        ⟨cellsBeforeInclusion (Operad.CellsAt c) h x.1, x.2⟩ := by
  erw [sphereCoproductDegreeBasis_apply, sphereCoproductDegreeBasis_apply]
  change ((Sigma.ι (Operad.cellStageGeneratorSpheres c j) x.1 ≫
    Operad.cellStageGeneratorCoproductMap c h).f i) _ = _
  rw [Operad.cellStageGeneratorCoproductMap, Sigma.ι_comp_desc]
  rfl

/-- The generator coproduct map preserves the globally chosen cell weights. -/
lemma cellStageGeneratorCoproductMap_preserves (hX : IsInitial X) {j k : J} (h : j ≤ k) :
    (cellStageGeneratorWeightBasis c hX j).Preserves (cellStageGeneratorWeightBasis c hX k)
      (Operad.cellStageGeneratorCoproductMap c h) := by
  intro i N x hx
  apply map_mem_basisWeightSpan
    ((cellStageGeneratorWeightBasis c hX j).basis i)
    ((cellStageGeneratorWeightBasis c hX k).basis i)
    (fun z => (cellStageGeneratorWeightBasis c hX j).weight ⟨i, z⟩)
    (fun z => (cellStageGeneratorWeightBasis c hX k).weight ⟨i, z⟩)
    ((Operad.cellStageGeneratorCoproductMap c h).f i).hom ?_ N hx
  intro z
  rw [cellStageGeneratorCoproductMap_basis c hX h]
  exact basis_mem_basisWeightSpan ((cellStageGeneratorWeightBasis c hX k).basis i)
    (fun z => (cellStageGeneratorWeightBasis c hX k).weight ⟨i, z⟩)
    ⟨cellsBeforeInclusion (Operad.CellsAt c) h z.1, z.2⟩

/-- The actual map from a cell stage to a later stage preserves all word weight bounds. -/
lemma cellStageMap_preserves (hX : IsInitial X) {j k : J} (h : j ≤ k) :
    (cellStageWeightBasis c hX j).Preserves (cellStageWeightBasis c hX k)
      (c.F.map (homOfLE h)).hom := by
  intro i N x hx
  let b := cellStageGeneratorWeightBasis c hX j
  let d := cellStageGeneratorWeightBasis c hX k
  let ej := Operad.cellStageSchurDegreeIso c hX j i
  let ek := Operad.cellStageSchurDegreeIso c hX k i
  have hs := (mem_basisWeightSpan_iff_map (cellStageWordBasis c hX j i)
    (schurWordBasis b.basis i) ej.toLinearEquiv (cellStageWordBasis_compare c hX j i)
    (cellStageBasisWeight c hX j i) N x).mp hx
  have ht := preserves_schurMap (cellStageGeneratorCoproductMap_preserves c hX h) i N hs
  apply (mem_basisWeightSpan_iff_map (cellStageWordBasis c hX k i)
    (schurWordBasis d.basis i) ek.toLinearEquiv (cellStageWordBasis_compare c hX k i)
    (cellStageBasisWeight c hX k i) N _).mpr
  have he := congrArg (fun z => z.hom.f i x)
    (Operad.cellStageErasedFreeIso_naturality c hX h)
  change ek.hom ((c.F.map (homOfLE h)).hom.f i x) =
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).map (Operad.cellStageGeneratorCoproductMap c h)).f i
      (ej.hom x) at he
  change ek.hom ((c.F.map (homOfLE h)).hom.f i x) ∈ _
  rw [he]
  exact ht

end SerrePositivity.EInfinity.BarrattEccles
