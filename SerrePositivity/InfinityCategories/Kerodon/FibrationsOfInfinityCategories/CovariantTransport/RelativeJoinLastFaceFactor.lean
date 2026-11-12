module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderConeAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderLastVertexStep

/-!
概要：最後の頂点を保たない標準単体の射の最後の面への因子化。
方針：頂点写像の単調性で像を小さい標準単体に制限し、円柱比較の二つの帰納段階を統合する。
規約：小さい終域の比較と同じ終域の境界の比較を帰納仮定とする。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、標準単体間の射の比較。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：最後の頂点を最後へ送らない射は終域の最後の面を経由する。
方針：全頂点の像が終域の最後の頂点より小さいことを単調性から示し、Yoneda で射に戻す。
規約：終域の次元は n+1。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、f(m)<n の場合の終域の次元降下。 -/
lemma relativeJoin_exists_lastFaceFactor {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n + 1])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) ≠ Fin.last (n + 1)) :
    ∃ g : (Δ[m] : SSet.{u}) ⟶ Δ[n],
      g ≫ stdSimplex.δ (Fin.last (n + 1)) = f := by
  let φ := SSet.yonedaEquiv f
  have hlast : (φ (Fin.last m)).val < n + 1 := by
    have hn : (φ (Fin.last m)).val ≠ n + 1 := by
      intro h
      exact hf (Fin.ext h)
    have := (φ (Fin.last m)).isLt
    omega
  have hbound (i : Fin (m + 1)) : (φ i).val < n + 1 := by
    have h := stdSimplex.monotone_apply φ (Fin.le_last i)
    change (φ i).val ≤ (φ (Fin.last m)).val at h
    omega
  let ψ : Fin (m + 1) →o Fin (n + 1) :=
    ⟨fun i ↦ ⟨(φ i).val, hbound i⟩, fun i j hij ↦ stdSimplex.monotone_apply φ hij⟩
  let a : (Δ[n] : SSet.{u}) _⦋m⦌ := stdSimplex.objMk ψ
  refine ⟨SSet.yonedaEquiv.symm a, ?_⟩
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  apply stdSimplex.ext
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_stdSimplex_hom_apply]
  change (Fin.last (n + 1)).succAbove (ψ i) = φ i
  rw [Fin.succAbove_last]
  apply Fin.ext
  rfl

/-- 概要：最後の頂点を保たない射の円柱比較は小さい終域の比較から従う。
方針：最後の面への因子化を取り、右錐による帰納段階を適用する。
規約：小さい終域への全ての標準 m 単体の射の比較を仮定する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、終域の次元に関する帰納。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_of_not_last
    {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n + 1])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) ≠ Fin.last (n + 1))
    (hsmall : ∀ g : (Δ[m] : SSet.{u}) ⟶ Δ[n],
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison f) := by
  obtain ⟨g, rfl⟩ := relativeJoin_exists_lastFaceFactor f hf
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison_lastFace g (hsmall g)

/-- 概要：標準単体の射の円柱比較は小さい終域と始域の境界の比較から従う。
方針：最後の頂点を保つ場合と保たない場合で二つの帰納段階を適用する。
規約：境界の比較は現在の射についてだけ要求する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、始域のセル分解と終域の次元の帰納の接続。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_stdSimplex_step
    {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n + 1])
    (hsmall : ∀ g : (Δ[m] : SSet.{u}) ⟶ Δ[n],
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison g))
    (hboundary : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison ((boundary m).ι ≫ f))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison f) := by
  by_cases hf : (SSet.yonedaEquiv f) (Fin.last m) = Fin.last (n + 1)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison_lastVertex_of_boundary
      f hf hboundary
  · exact isPrecompositionEquivalence_relativeJoinCylinderComparison_of_not_last f hf hsmall

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
