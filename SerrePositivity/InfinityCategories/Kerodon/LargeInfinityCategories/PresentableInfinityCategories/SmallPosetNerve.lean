module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces

/-!
概要：元の μ-small thin 圏の nerve が、非退化単体の個数でも μ-small であること。
方針：各単体を有限列へ埋め込み、明示的な冪の評価と正則性で全次数を数える。
規約：単に各次数が小さいだけでは終えず、全非退化単体を同じ μ で評価する。
使われ方：濃度変更の部分表示を元の IsKappaSmall で検査する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 明示的な冪の評価のもとで、小さい thin 圏の nerve の全非退化単体も小さい。 -/
lemma isKappaSmall_nerve_of_cardinalChangeBound {κ μ : Cardinal.{u}}
    [Fact κ.IsRegular] [Fact μ.IsRegular] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    (I : Type u) [SmallCategory I] [Quiver.IsThin I] (hI : HasCardinalLT I μ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (nerve I) := by
  have hNat : HasCardinalLT (ULift.{u} ℕ) μ := by
    rw [hasCardinalLT_iff_cardinal_mk_lt]
    simpa only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0] using
      (Cardinal.IsRegular.aleph0_le (Fact.out : κ.IsRegular)).trans_lt h.1
  have hEach (n : ℕ) : HasCardinalLT ((nerve I) _⦋n⦌) μ := by
    have hα : Cardinal.mk (ULift.{u} (Fin (n + 1))) < κ :=
      (hasCardinalLT_iff_cardinal_mk_lt _ _).mp
        (hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le (Fact.out : κ.IsRegular)))
    have hFun : HasCardinalLT (ULift.{u} (Fin (n + 1)) → I) μ := by
      rw [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_arrow]
      simpa only [Cardinal.lift_id] using h.2 _ _ hα
        ((hasCardinalLT_iff_cardinal_mk_lt _ _).mp hI)
    apply hFun.of_injective (fun s i ↦ s.obj i.down)
    intro s t hs
    exact ComposableArrows.ext (fun i ↦ congrFun hs (ULift.up i))
      (fun _ _ ↦ Subsingleton.elim _ _)
  have hAll : HasCardinalLT (Σ n : ULift.{u} ℕ, (nerve I) _⦋n.down⦌) μ :=
    hasCardinalLT_sigma _ μ hNat (fun n ↦ hEach n.down)
  have hN : HasCardinalLT (nerve I).N μ := hAll.of_injective
    (fun s ↦ ⟨ULift.up s.dim, s.simplex⟩) (by
      rintro ⟨⟨n, s⟩, hs⟩ ⟨⟨m, t⟩, ht⟩ he
      cases he
      rfl)
  exact (hasCardinalLT_iff_cardinal_mk_lt _ _).mp hN

/-- 各小さい filtered 部分集合の同じ nerve は、filtered 性と元の形状の小ささを両方持つ。 -/
lemma smallFilteredPiece_nerve_properties {κ μ : Cardinal.{u}}
    [Fact κ.IsRegular] [Fact μ.IsRegular] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {I : Type u} [PartialOrder I] (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (nerve A.val) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (nerve A.val) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallFilteredPiece_nerve_isKappaFiltered A,
    isKappaSmall_nerve_of_cardinalChangeBound h A.val A.property.2⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
