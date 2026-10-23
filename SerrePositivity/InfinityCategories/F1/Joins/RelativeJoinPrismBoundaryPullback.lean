module

public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinPrismCoverage
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinBoundaryMissingVertex

/-!
概要：prism 比較に沿う境界 relative join の逆像は Z(m)。
方針：prism を Z(m) と最後のセルで覆い、欠ける左の頂点から最後のセルのホーンを検出する。
規約：終域は任意、標準単体であることは始域にだけ要求する。
使われ方：Kerodon Proposition 5.2.4.5、比較の立方体の後面の交わりの同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：最後の prism の最大単体の零側は係数の全ての頂点を一度ずつ通る。
方針：切替位置が最後である場合の時刻と係数の頂点の式を使う。
規約：v.castSucc が零側の v 番目の頂点。
使われ方：Kerodon Proposition 5.2.4.5、境界の逆像の最後のセルでの検査。 -/
lemma relativeJoinPrismShuffle_last_left_vertex (m : ℕ) (v : Fin (m + 1)) :
    ((relativeJoinPrismShuffle.{u} m (Fin.last m)).1 v.castSucc,
      (relativeJoinPrismShuffle.{u} m (Fin.last m)).2 v.castSucc) = (0, v) := by
  refine Prod.ext ?_ ?_
  · apply Fin.ext
    exact (relativeJoinPrismShuffle_time_zero_iff.{u} m (Fin.last m) v.castSucc).mpr
      (by change v.val ≤ m; exact Nat.le_of_lt_succ v.isLt)
  · apply Fin.ext
    rw [relativeJoinPrismShuffle_coefficient_val,
      ite_eq_left (by change v.val ≤ m; exact Nat.le_of_lt_succ v.isLt)]
    rfl

/-- 概要：最後のセルで比較像が境界に入る単体は最後のホーンに入る。
方針：零時刻の欠ける係数頂点に対応するセルの頂点が元の単体の像から欠けることを使う。
規約：ホーンの欠ける面は最後の頂点である。
使われ方：Kerodon Proposition 5.2.4.5、Z(m) 以外の単体が境界へ入らないことの検査。 -/
lemma relativeJoinPrism_last_boundary_mem_horn {Y : SSet.{u}} {m d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) (a : (Δ[m + 1] : SSet.{u}) _⦋d⦌)
    (h : (relativeJoinPrism f).app (Opposite.op ⦋d⦌)
        ((SSet.yonedaEquiv.symm (relativeJoinPrismShuffle m (Fin.last m))).app
          (Opposite.op ⦋d⦌) a) ∈ Set.range
      ((relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl).app (Opposite.op ⦋d⦌))) :
    a ∈ (horn (m + 1) (Fin.last m).succ).obj (Opposite.op ⦋d⦌) := by
  obtain ⟨v, hv⟩ := relativeJoinPrism_boundary_exists_missing_vertex f _ _ h
  apply (mem_horn_iff_notMem_range a (Fin.last m).succ).mpr
  refine ⟨v.castSucc, ?_, ?_⟩
  · intro he
    have hh := congrArg Fin.val he
    have := v.isLt
    change v.val = m + 1 at hh
    omega
  · rintro ⟨i, hi⟩
    have he := relativeJoinPrismShuffle_last_left_vertex.{u} m v
    apply hv i
    · change ((relativeJoinPrismShuffle.{u} m (Fin.last m)).1 (a i)).val = 0
      rw [hi]
      exact congrArg (fun p : Fin 2 × Fin (m + 1) ↦ p.1.val) he
    · change (relativeJoinPrismShuffle.{u} m (Fin.last m)).2 (a i) = v
      rw [hi]
      exact congrArg Prod.snd he

/-- 概要：prism 比較による境界 relative join の逆像は Z(m)。
方針：Z(m) からの包含と、最後のセルのホーンによる逆向きの包含を合わせる。
規約：構造射 f の終域には追加の条件を要求しない。
使われ方：Kerodon Proposition 5.2.4.5、境界と prism の交わりの同定。 -/
lemma relativeJoinPrism_boundary_preimage_eq_penultimate {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    (Subcomplex.range (relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl)).preimage (relativeJoinPrism f) =
      relativeJoinPrismPenultimate m := by
  apply le_antisymm
  · rintro ⟨⟨d⟩⟩ z hz
    rcases relativeJoinPrismPenultimate_or_last m d z with h | ⟨a, rfl⟩
    · exact h
    · have ha := relativeJoinPrism_last_boundary_mem_horn f a hz
      have he := relativeJoinPrismStage_preimage_shuffle_eq_horn.{u} m (Fin.last m)
      have hb := (congrArg (fun P ↦ a ∈ P.obj (Opposite.op ⦋d⦌)) he).mpr ha
      change (SSet.yonedaEquiv.symm (relativeJoinPrismShuffle m (Fin.last m))).app
        (Opposite.op ⦋d⦌) a ∈ (relativeJoinPrismStage m m).obj (Opposite.op ⦋d⦌) at hb
      simpa only [relativeJoinPrismStage_penultimate] using hb
  · exact relativeJoinPrismPenultimate_le_boundary_preimage f

/-- 概要：Z(m) と境界 relative join の比較の正方形は pullback。
方針：境界への包含の単射性と逆像の等式から、各次数の持ち上げを作る。
規約：prism 比較自体の単射性は仮定しない。
使われ方：Kerodon Proposition 5.2.4.5、後面の pushout の型ごとの判定への入力。 -/
lemma relativeJoinPrismPenultimateBoundaryLift_isPullback {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    IsPullback (relativeJoinPrismPenultimateBoundaryLift f) (relativeJoinPrismPenultimate m).ι
      (relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl)
      (relativeJoinPrism f) := by
  apply IsPullback.of_forall_isPullback_app
  intro n
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨congrArg (fun k : (relativeJoinPrismPenultimate m : SSet.{u}) ⟶
    relativeJoin f (𝟙 Y) ↦ k.app n) (relativeJoinPrismPenultimateBoundaryLift_comp f), ?_, ?_⟩
  · intro x y h
    exact Subtype.ext h.2
  · intro b z h
    have hz : z ∈ (relativeJoinPrismPenultimate m).obj n := by
      have he := relativeJoinPrism_boundary_preimage_eq_penultimate f
      apply (congrArg (fun P ↦ z ∈ P.obj n) he).mp
      exact ⟨b, h⟩
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    apply (mono_iff_injective ((relativeJoinLeftMap (𝟙 Y)
      (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl).app n)).mp inferInstance
    have he := congrArg (fun k : (relativeJoinPrismPenultimate m : SSet.{u}) ⟶
      relativeJoin f (𝟙 Y) ↦ k.app n ⟨z, hz⟩) (relativeJoinPrismPenultimateBoundaryLift_comp f)
    exact he.trans h.symm

end SerrePositivity.InfinityCategories
