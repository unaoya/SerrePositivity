module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairRightRepresentability
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftFibrationInitialEvaluation

/-!
概要：全関手 coslice の元の始対象性を保存条件付きの制限へ移す。
方針：始対象の境界充填を元の全空間で行い、境界の全頂点の所属から全部分圏へ戻す。
規約：全関手圏の保存条件以外の射の条件を追加しない。
使われ方：単位の二変数族の実際の相対評価。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：全部分圏への底の制限は、元の始対象を保持する。
方針：全空間の境界充填の射影を、その全頂点の所属を使って元の全部分圏に持ち上げる。
規約：始対象の辺や高次単体を商にしない。quasicategory 性は不要。
使われ方：元の随伴単位の始対象性を保存関手圏へ移す。 -/
lemma initialVertex_pullback_fullSubcomplex {E B : SSet.{u}} (p : E ⟶ B)
    (P : B _⦋0⦌ → Prop)
    (x : (pullback p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B P).ι) _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex ((pullback.fst p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B P).ι).app
      (Opposite.op ⦋0⦌) x)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x := by
  let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B P).ι
  let f := pullback.fst p j
  let g := pullback.snd p j
  intro n b hb
  have hbf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ (b ≫ f) =
      SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
  obtain ⟨F, hF⟩ := hx n (b ≫ f) hbf
  have hv : ∀ v, P ((F ≫ p).app (Opposite.op ⦋0⦌) v) := by
    intro v
    have hvb : v ∈ (boundary (n + 1)).obj (Opposite.op ⦋0⦌) := by
      have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n (SSet.stdSimplex.obj₀Equiv v)
      rwa [Equiv.symm_apply_apply] at h
    let t : (boundary (n + 1) : SSet.{u}) _⦋0⦌ := ⟨v, hvb⟩
    have h := congrArg (fun k : (boundary (n + 1) : SSet.{u}) ⟶ B ↦
      k.app (Opposite.op ⦋0⦌) t) (congrArg (· ≫ p) hF)
    have hg : (b ≫ f) ≫ p = (b ≫ g) ≫ j := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (b ≫ ·) pullback.condition
    rw [hg] at h
    change (F ≫ p).app (Opposite.op ⦋0⦌) v =
      ((b ≫ g).app (Opposite.op ⦋0⦌) t).val at h
    rw [h]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex ((b ≫ g).app _ t)
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P (F ≫ p) hv
  have hG : G ≫ j = F ≫ p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  let L := pullback.lift F G hG.symm
  refine ⟨L, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact hF
  · apply (cancel_mono j).mp
    have hLg : L ≫ g = G := pullback.lift_snd _ _ _
    calc
      (((boundary (n + 1)).ι ≫ L) ≫ g) ≫ j =
          (boundary (n + 1)).ι ≫ ((L ≫ g) ≫ j) := by simp only [Category.assoc]
      _ = (boundary (n + 1)).ι ≫ (G ≫ j) := by rw [hLg]
      _ = ((boundary (n + 1)).ι ≫ F) ≫ p := by rw [hG, Category.assoc]
      _ = (b ≫ f) ≫ p := by rw [hF]
      _ = (b ≫ g) ≫ j := by
        rw [Category.assoc, Category.assoc]
        exact congrArg (b ≫ ·) pullback.condition

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
