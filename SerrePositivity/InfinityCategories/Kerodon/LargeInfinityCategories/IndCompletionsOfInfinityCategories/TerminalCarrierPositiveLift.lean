module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalCarrierVertex

/-!
概要：終頂点を指定した鎖の実現空間の射影は、全ての正次元境界を持ち上げる。
方針：境界全体を最後の部分複体に因子分解し、その指定終頂点で充填する。
規約：元の境界と鎖を厳密に保つ。零次元は別途指定頂点から与える。
使われ方：射影の trivial Kan fibration 性と実際の切断。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Preorder I] {X : SSet.{u}}

/-- 同じ終頂点の条件は、鎖の実現空間の正次元境界を全て持ち上げる。 -/
lemma terminalCarrier_exists_positive_lift (A : I → X.Subcomplex) (hA : Monotone A)
    (t : ∀ i, (A i).toSSet _⦋0⦌) (ht : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (t i))
    (n : ℕ) (b : (boundary (n + 1) : SSet.{u}) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A (fun i => (t i).val)).toSSet)
    (q : (Δ[n + 1] : SSet.{u}) ⟶ nerve I)
    (h : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection A (fun i => (t i).val) = (boundary (n + 1)).ι ≫ q) :
    ∃ G : (Δ[n + 1] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A (fun i => (t i).val)).toSSet,
      (boundary (n + 1)).ι ≫ G = b ∧ G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection A (fun i => (t i).val) = q := by
  let z := fun i => (t i).val
  let j := (SSet.yonedaEquiv q).obj (Fin.last (n + 1))
  let b' : (boundary (n + 1) : SSet.{u}) ⟶ (A j).toSSet :=
    Subcomplex.lift (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierValue A z)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierValue_range_le hA b (boundary (n + 1)).ι q h)
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b' = SSet.yonedaEquiv.symm (t j) := by
    apply (cancel_mono (A j).ι).mp
    have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierValue_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b)
    have hq : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection A z =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.lastVertexMap (n + 1) ≫ q := by
      rw [Category.assoc, h, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.boundaryLastVertex_ι]
    rw [hq, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.nerveHom_lastVertex] at hb
    calc
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b') ≫ (A j).ι =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierValue A z := by
        rw [Category.assoc, Subcomplex.lift_ι, ← Category.assoc]
      _ = SSet.yonedaEquiv.symm (t j).val := hb
      _ = SSet.yonedaEquiv.symm (t j) ≫ (A j).ι :=
        (SSet.yonedaEquiv_symm_comp (t j) (A j).ι).symm
  obtain ⟨F', hF'⟩ := ht j n b' hv
  let F := F' ≫ (A j).ι
  have hpair : (boundary (n + 1)).ι ≫ lift F q = b ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).ι := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst]
      change (boundary (n + 1)).ι ≫ (F' ≫ (A j).ι) = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierValue A z
      rw [← Category.assoc, hF']
      exact Subcomplex.lift_ι _ _
    · rw [Category.assoc, lift_snd]
      exact h.symm
  have hx : SSet.yonedaEquiv F ∈ (A j).obj _ := (SSet.yonedaEquiv F').property
  let hp := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierCondition_of_filler b F q hpair hx
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierSimplex F q hp, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierSimplex_projection F q hp⟩
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).ι).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierSimplex_ι]
  exact hpair

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
