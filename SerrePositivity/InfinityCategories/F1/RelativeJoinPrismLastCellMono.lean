module

public import SerrePositivity.InfinityCategories.F1.RelativeJoinPrismBoundaryPullback

/-!
概要：標準単体上の prism 比較の最後のセルの単射性と境界の外での単射性。
方針：通常の join の頂点番号の左右の区間を区別し、最後のセルの元の頂点を回復する。
規約：終域が標準単体であることを要求し、最後の頂点の像には条件を課さない。
使われ方：Kerodon Proposition 5.2.4.5、比較の後面の pushout の単射判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：標準単体上の prism 比較を最後の最大単体に制限すると単射になる。
方針：join の左側では係数が元の頂点、右側では元の頂点が最後であることを使う。
規約：射 f の最後の頂点での値の条件は不要。
使われ方：Kerodon Proposition 5.2.4.5、prism の境界の外での単射性。 -/
instance relativeJoinPrism_lastCell_mono {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    Mono (SSet.yonedaEquiv.symm (relativeJoinPrismShuffle m (Fin.last m)) ≫
      relativeJoinPrism f) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨d⟩⟩
  rw [mono_iff_injective]
  intro a b h
  let s := SSet.yonedaEquiv.symm (relativeJoinPrismShuffle.{u} m (Fin.last m))
  let za := s.app (Opposite.op ⦋d⦌) a
  let zb := s.app (Opposite.op ⦋d⦌) b
  have he : (joinCylinderMap Δ[m] Δ[n]).app (Opposite.op ⦋d⦌)
      ((za.2, za.1), f.app _ za.2) =
      (joinCylinderMap Δ[m] Δ[n]).app (Opposite.op ⦋d⦌) ((zb.2, zb.1), f.app _ zb.2) := by
    rw [← relativeJoinPrism_fst_app, ← relativeJoinPrism_fst_app]
    exact congrArg (fun z ↦ (pullback.fst (joinMap f (𝟙 Δ[n])) (joinDiagonal Δ[n])).app
      (Opposite.op ⦋d⦌) z) h
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  have hv := congrArg (fun z : join (Δ[m] : SSet.{u}) Δ[n] _⦋d⦌ ↦
    ((joinStdSimplexIso m n).hom.app (Opposite.op ⦋d⦌) z i).val) he
  rw [joinCylinderMap_stdSimplex_val, joinCylinderMap_stdSimplex_val] at hv
  have hta : (za.1 i).val = 0 ↔ (a i).val ≤ m :=
    relativeJoinPrismShuffle_time_zero_iff.{u} m (Fin.last m) (a i)
  have htb : (zb.1 i).val = 0 ↔ (b i).val ≤ m :=
    relativeJoinPrismShuffle_time_zero_iff.{u} m (Fin.last m) (b i)
  have hca : (za.2 i).val = if (a i).val ≤ m then (a i).val else (a i).val - 1 :=
    relativeJoinPrismShuffle_coefficient_val.{u} m (Fin.last m) (a i)
  have hcb : (zb.2 i).val = if (b i).val ≤ m then (b i).val else (b i).val - 1 :=
    relativeJoinPrismShuffle_coefficient_val.{u} m (Fin.last m) (b i)
  simp only [hta, htb, hca, hcb] at hv
  have ha := (a i).isLt
  have hb := (b i).isLt
  split_ifs at hv <;> omega

/-- 概要：標準単体上の prism 比較は Z(m) の外で各次数の単体について単射。
方針：外にある二つの単体を最後のセルへ持ち上げ、その制限の単射性を使う。
規約：元の prism 比較全体の単射性は主張しない。
使われ方：Kerodon Proposition 5.2.4.5、境界と prism の pushout の型ごとの検査。 -/
lemma relativeJoinPrism_injective_outside_penultimate {m n d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (x y : ((Δ[1] : SSet.{u}) ⊗ Δ[m]) _⦋d⦌)
    (hx : x ∉ (relativeJoinPrismPenultimate m).obj (Opposite.op ⦋d⦌))
    (hy : y ∉ (relativeJoinPrismPenultimate m).obj (Opposite.op ⦋d⦌))
    (h : (relativeJoinPrism f).app (Opposite.op ⦋d⦌) x =
      (relativeJoinPrism f).app (Opposite.op ⦋d⦌) y) : x = y := by
  obtain hx' | ⟨a, rfl⟩ := relativeJoinPrismPenultimate_or_last m d x
  · exact (hx hx').elim
  obtain hy' | ⟨b, rfl⟩ := relativeJoinPrismPenultimate_or_last m d y
  · exact (hy hy').elim
  have he : a = b := (mono_iff_injective
    ((SSet.yonedaEquiv.symm (relativeJoinPrismShuffle m (Fin.last m)) ≫
      relativeJoinPrism f).app (Opposite.op ⦋d⦌))).mp inferInstance h
  exact congrArg _ he

end SerrePositivity.InfinityCategories
