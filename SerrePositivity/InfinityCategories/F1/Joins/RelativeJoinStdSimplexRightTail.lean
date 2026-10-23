module

public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinStdSimplexVertices
public import SerrePositivity.InfinityCategories.F1.Joins.JoinDiagonalEndpoint

/-!
概要：最後の頂点を保つ標準単体間の射の relative join の境界外の右成分。
方針：左の最後の頂点を選び、その底での像と単調性から右成分を終端頂点に固定する。
規約：引き戻しの条件を通常の join の単体の等式で書く。
使われ方：Kerodon Proposition 5.2.4.5、境界と最後の prism セルによる被覆。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：左の境界に入らない relative join の単体の右成分は終端頂点に定値。
方針：左の最後の頂点の底での値を計算し、それ以降の値を単調性で固定する。
規約：f が最後の頂点を最後へ送ることを要求する。
使われ方：Kerodon Proposition 5.2.4.5、最後の prism セルで表せる単体の特徴づけ。 -/
lemma relativeJoin_stdSimplex_right_tail_last {m n d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) = Fin.last n)
    (s : Join.Simplex (Δ[m] : SSet.{u}) Δ[n] d)
    (t : (Δ[1] : SSet.{u}) _⦋d⦌) (c : (Δ[n] : SSet.{u}) _⦋d⦌)
    (h : (joinMap f (𝟙 Δ[n])).app (Opposite.op ⦋d⦌) s =
      (joinDiagonal Δ[n]).app (Opposite.op ⦋d⦌) (t, c))
    (hs : s ∉ (joinSubcomplexLeft (boundary m) Δ[n]).obj (Opposite.op ⦋d⦌)) :
    ∀ j : Fin (d + 1 - s.1.val), Join.stdAugEquiv n _ s.2.2 j = Fin.last n := by
  obtain ⟨i, hi⟩ := relativeJoin_not_left_boundary_surjective s hs (Fin.last m)
  let p := Join.prefixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) i
  have hcut : s.1.val = Join.pullCut (stdSimplex.objEquiv t).toOrderHom 1 := by
    have he := congrArg (fun z : Join.Simplex (Δ[n] : SSet.{u}) Δ[n] d ↦ z.1.val) h
    exact he.trans (joinDiagonal_app_cut Δ[n] d t c)
  have hp : (t p).val = 0 := by
    have he : p.val < Join.pullCut (stdSimplex.objEquiv t).toOrderHom 1 := hcut ▸ i.isLt
    have ht := (Join.lt_pullCut_iff (stdSimplex.objEquiv t).toOrderHom 1 p).mp he
    change (t p).val < 1 at ht
    omega
  have hleft : (c p).val = n := by
    have he := congrArg (fun z : Join.Simplex (Δ[n] : SSet.{u}) Δ[n] d ↦
      ((joinStdSimplexIso n n).hom.app (Opposite.op ⦋d⦌) z p).val) h
    have hl := relativeJoin_stdSimplex_join_prefix_val
      ((joinMap f (𝟙 Δ[n])).app (Opposite.op ⦋d⦌) s) i
    have hd := joinDiagonal_stdSimplex_val n d t c p
    rw [ite_eq_left hp] at hd
    have hv : (Join.stdAugEquiv n s.1.val (Join.augHom f _ s.2.1) i).val = n := by
      rw [relativeJoin_stdAugHom_apply, hi, hf]
      rfl
    exact hd.symm.trans (he.symm.trans (hl.trans hv))
  intro j
  let q := Join.suffixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) j
  have hpq : p ≤ q := by
    change i.val ≤ s.1.val + j.val
    have := i.isLt
    omega
  have hcq : (c q).val = n := by
    have hm := stdSimplex.monotone_apply c hpq
    have hb := (c q).isLt
    change (c p).val ≤ (c q).val at hm
    omega
  have hq : (t q).val ≠ 0 := by
    intro hz
    have he := (Join.lt_pullCut_iff (stdSimplex.objEquiv t).toOrderHom 1 q).mpr
      (show (t q).val < 1 by omega)
    rw [← hcut] at he
    change s.1.val + j.val < s.1.val at he
    omega
  have he := congrArg (fun z : Join.Simplex (Δ[n] : SSet.{u}) Δ[n] d ↦
    ((joinStdSimplexIso n n).hom.app (Opposite.op ⦋d⦌) z q).val) h
  have hr := relativeJoin_stdSimplex_join_suffix_val
    ((joinMap f (𝟙 Δ[n])).app (Opposite.op ⦋d⦌) s) j
  have hd := joinDiagonal_stdSimplex_val n d t c q
  rw [ite_eq_right hq] at hd
  have hv : n + 1 + (Join.stdAugEquiv n _ s.2.2 j).val = n + 1 + (c q).val := by
    have hr' : ((joinStdSimplexIso n n).hom.app (Opposite.op ⦋d⦌)
        ((joinMap f (𝟙 Δ[n])).app (Opposite.op ⦋d⦌) s) q).val =
        n + 1 + (Join.stdAugEquiv n _ s.2.2 j).val := by
      change ((joinStdSimplexIso n n).hom.app (Opposite.op ⦋d⦌)
        ((joinMap f (𝟙 Δ[n])).app (Opposite.op ⦋d⦌) s) q).val =
          n + 1 + (Join.stdAugEquiv n _ (Join.augHom (𝟙 Δ[n]) _ s.2.2) j).val at hr
      simpa only [Join.augHom_id] using hr
    exact hr'.symm.trans (he.trans hd)
  apply Fin.ext
  change (Join.stdAugEquiv n _ s.2.2 j).val = n
  omega

/-- 概要：最後の頂点を保つ場合の最後のセルの比較像の頂点番号。
方針：零側では元の頂点、右側では終域の最後の頂点に写ることを計算する。
規約：通常の join を標準 m+n+1 単体と同定して番号を読む。
使われ方：Kerodon Proposition 5.2.4.5、右成分が終端の単体の最後のセルへの持ち上げ。 -/
lemma relativeJoinPrism_lastCell_stdSimplex_val {m n d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) = Fin.last n)
    (a : (Δ[m + 1] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    ((joinStdSimplexIso m n).hom.app (Opposite.op ⦋d⦌)
      ((pullback.fst (joinMap f (𝟙 Δ[n])) (joinDiagonal Δ[n])).app (Opposite.op ⦋d⦌)
        ((relativeJoinPrism f).app (Opposite.op ⦋d⦌)
          ((SSet.yonedaEquiv.symm (relativeJoinPrismShuffle m (Fin.last m))).app
            (Opposite.op ⦋d⦌) a))) i).val =
      if (a i).val ≤ m then (a i).val else m + 1 + n := by
  let z := (SSet.yonedaEquiv.symm (relativeJoinPrismShuffle.{u} m (Fin.last m))).app
    (Opposite.op ⦋d⦌) a
  change ((joinStdSimplexIso m n).hom.app (Opposite.op ⦋d⦌)
    ((pullback.fst (joinMap f (𝟙 Δ[n])) (joinDiagonal Δ[n])).app (Opposite.op ⦋d⦌)
      ((relativeJoinPrism f).app (Opposite.op ⦋d⦌) (z.1, z.2))) i).val = _
  rw [relativeJoinPrism_fst_app, joinCylinderMap_stdSimplex_val]
  have ht : (z.1 i).val = 0 ↔ (a i).val ≤ m :=
    relativeJoinPrismShuffle_time_zero_iff.{u} m (Fin.last m) (a i)
  have hc : (z.2 i).val = if (a i).val ≤ m then (a i).val else (a i).val - 1 :=
    relativeJoinPrismShuffle_coefficient_val.{u} m (Fin.last m) (a i)
  simp only [ht, hc]
  split_ifs with ha
  · rfl
  · have he : z.2 i = Fin.last m := by
      apply Fin.ext
      rw [hc, ite_eq_right ha]
      have hb := (a i).isLt
      change (a i).val - 1 = m
      omega
    rw [relativeJoin_stdSimplex_hom_apply, he, hf]
    rfl

end SerrePositivity.InfinityCategories
