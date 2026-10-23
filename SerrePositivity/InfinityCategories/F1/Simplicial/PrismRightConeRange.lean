module

public import SerrePositivity.InfinityCategories.F1.Simplicial.PrismRightConeMap
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinStdSimplexVertices

/-!
概要：prism の右錐の比較の像の単体ごとの判定。
方針：係数の最後の頂点の手前で切断し、前半の時刻と係数を対にして戻す。
規約：最後の係数頂点では時刻が一である単体を扱う。
使われ方：Kerodon Proposition 5.2.4.5、右錐の比較の全射性のための底の持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：prism の右錐の比較の時刻は先頭区間で元の時刻を読む。
方針：区間と点の join の左区間の頂点番号に退化を適用する。
規約：r は当該単体の切断。
使われ方：Kerodon Proposition 5.2.4.5、底の持ち上げの前半の時刻の検査。 -/
lemma prismRightConeMap_time_prefix {n d : ℕ}
    (s : Join.Simplex ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] d) (i : Fin s.1.val) :
    ((prismRightConeMap n).app (Opposite.op ⦋d⦌) s).1
        (Join.prefixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) i) =
      Join.stdAugEquiv 1 _ (Join.augHom (fst (Δ[1] : SSet.{u}) Δ[n]) _ s.2.1) i := by
  let p := Join.prefixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) i
  let a := (joinMap (fst (Δ[1] : SSet.{u}) Δ[n]) (𝟙 Δ[0])).app (Opposite.op ⦋d⦌) s
  let w := (joinStdSimplexIso.{u} 1 0).hom.app (Opposite.op ⦋d⦌) a p
  let v := Join.stdAugEquiv 1 _ (Join.augHom (fst (Δ[1] : SSet.{u}) Δ[n]) _ s.2.1) i
  have hw : w.val = v.val := relativeJoin_stdSimplex_join_prefix_val a i
  have hv := v.isLt
  have hle : w ≤ (1 : Fin 2).castSucc := by change w.val ≤ 1; omega
  change (1 : Fin 2).predAbove w = v
  rw [Fin.predAbove_of_le_castSucc _ _ hle]
  apply Fin.ext
  exact hw

/-- 概要：prism の右錐の比較の時刻は末尾区間で一。
方針：区間と点の join の右側の頂点二を退化で一へ送る。
規約：末尾区間の全頂点について成立する。
使われ方：Kerodon Proposition 5.2.4.5、底の持ち上げの後半の時刻の検査。 -/
lemma prismRightConeMap_time_suffix {n d : ℕ}
    (s : Join.Simplex ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] d)
    (i : Fin (d + 1 - s.1.val)) :
    ((prismRightConeMap n).app (Opposite.op ⦋d⦌) s).1
        (Join.suffixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) i) = 1 := by
  let p := Join.suffixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) i
  let a := (joinMap (fst (Δ[1] : SSet.{u}) Δ[n]) (𝟙 Δ[0])).app (Opposite.op ⦋d⦌) s
  let w := (joinStdSimplexIso.{u} 1 0).hom.app (Opposite.op ⦋d⦌) a p
  have hw := relativeJoin_stdSimplex_join_suffix_val a i
  have hv := (Join.stdAugEquiv 0 _ a.2.2 i).isLt
  have he : w = (2 : Fin 3) := by
    apply Fin.ext
    change w.val = 2
    change w.val = 1 + 1 + (Join.stdAugEquiv 0 _ a.2.2 i).val at hw
    omega
  change (1 : Fin 2).predAbove w = 1
  rw [he]
  rfl

/-- 概要：最後の係数頂点で時刻一となる単体は prism の右錐の比較の像に入る。
方針：係数の右錐表示の切断を使い、先頭の係数と時刻を対にして単体を作る。
規約：時刻と係数の順序写像を同じ切断で制限する。
使われ方：Kerodon Proposition 5.2.4.5、relative join の右錐への全射性の底の持ち上げ。 -/
lemma prismRightConeMap_mem_range {n d : ℕ}
    (t : (Δ[1] : SSet.{u}) _⦋d⦌) (c : (Δ[n + 1] : SSet.{u}) _⦋d⦌)
    (h : ∀ i : Fin (d + 1), c i = Fin.last (n + 1) → t i = 1) :
    (t, c) ∈ Set.range ((prismRightConeMap n).app (Opposite.op ⦋d⦌)) := by
  let s := (joinStdSimplexIso.{u} n 0).inv.app (Opposite.op ⦋d⦌) c
  let tp := Join.augMap (Δ[1] : SSet.{u})
    (Join.prefixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt)) t
  let z : Join.Simplex ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] d :=
    ⟨s.1, (Join.augTensorEquiv Δ[1] Δ[n] s.1.val).symm (tp, s.2.1), s.2.2⟩
  have hc : (joinStdSimplexIso.{u} n 0).hom.app (Opposite.op ⦋d⦌) s = c :=
    congrArg (fun k : (Δ[n + 1] : SSet.{u}) ⟶ Δ[n + 1] ↦ k.app (Opposite.op ⦋d⦌) c)
      (joinStdSimplexIso n 0).inv_hom_id
  have hb : (joinMap (snd (Δ[1] : SSet.{u}) Δ[n]) (𝟙 Δ[0])).app (Opposite.op ⦋d⦌) z = s := by
    refine Join.Simplex.ext _ _ (by rfl) ?_ ?_
    · exact Join.augTensorEquiv_symm_augHomSnd _ _ _ _ _
    · exact Join.augHom_id _ _ _
  refine ⟨z, ?_⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    by_cases hi : i.val < s.1.val
    · let j : Fin s.1.val := ⟨i.val, hi⟩
      have he := prismRightConeMap_time_prefix z j
      change ((prismRightConeMap n).app (Opposite.op ⦋d⦌) z).1 i =
        Join.stdAugEquiv 1 _ (Join.augHom (fst (Δ[1] : SSet.{u}) Δ[n]) _ z.2.1) j at he
      rw [Join.augTensorEquiv_symm_augHomFst, Join.stdAugEquiv_augMap] at he
      exact he
    · let j : Fin (d + 1 - s.1.val) := ⟨i.val - s.1.val, by have := i.isLt; omega⟩
      have hq : Join.suffixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) j = i := by
        apply Fin.ext
        change s.1.val + (i.val - s.1.val) = i.val
        omega
      have he := prismRightConeMap_time_suffix z j
      rw [hq] at he
      have hv := relativeJoin_stdSimplex_join_suffix_val s j
      rw [hq, hc] at hv
      have hp := (Join.stdAugEquiv 0 _ s.2.2 j).isLt
      have hci : c i = Fin.last (n + 1) := by apply Fin.ext; change (c i).val = n + 1; omega
      exact he.trans (h i hci).symm
  · change (joinStdSimplexIso.{u} n 0).hom.app (Opposite.op ⦋d⦌)
      ((joinMap (snd (Δ[1] : SSet.{u}) Δ[n]) (𝟙 Δ[0])).app (Opposite.op ⦋d⦌) z) = c
    rw [hb]
    exact hc

/-- 概要：prism の右錐の比較像は最後の係数頂点で時刻一となる。
方針：先頭区間の係数は最後より小さいため、最後の係数は末尾区間にだけ現れる。
規約：任意の単体の任意の頂点についての条件。
使われ方：Kerodon Proposition 5.2.4.5、右錐の底の像の必要条件。 -/
lemma prismRightConeMap_last_time_one {n d : ℕ}
    (s : Join.Simplex ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] d) (i : Fin (d + 1))
    (h : ((prismRightConeMap n).app (Opposite.op ⦋d⦌) s).2 i = Fin.last (n + 1)) :
    ((prismRightConeMap n).app (Opposite.op ⦋d⦌) s).1 i = 1 := by
  let a := (joinMap (snd (Δ[1] : SSet.{u}) Δ[n]) (𝟙 Δ[0])).app (Opposite.op ⦋d⦌) s
  by_cases hi : i.val < s.1.val
  · let j : Fin s.1.val := ⟨i.val, hi⟩
    have he := relativeJoin_stdSimplex_join_prefix_val a j
    change (((prismRightConeMap n).app (Opposite.op ⦋d⦌) s).2 i).val =
      (Join.stdAugEquiv n _ a.2.1 j).val at he
    rw [h] at he
    have hb := (Join.stdAugEquiv n _ a.2.1 j).isLt
    change n + 1 = (Join.stdAugEquiv n _ a.2.1 j).val at he
    omega
  · let j : Fin (d + 1 - s.1.val) := ⟨i.val - s.1.val, by have := i.isLt; omega⟩
    have hq : Join.suffixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) j = i := by
      apply Fin.ext
      change s.1.val + (i.val - s.1.val) = i.val
      omega
    have he := prismRightConeMap_time_suffix s j
    rw [hq] at he
    exact he

/-- 概要：prism の右錐の比較の像は最後の係数頂点で時刻一となる単体全体。
方針：比較像の必要条件と、切断による単体の持ち上げを合わせる。
規約：prism の単体を時刻 t と係数 c の対として表す。
使われ方：Kerodon Proposition 5.2.4.5、右錐の引き戻しの持ち上げの判定。 -/
lemma prismRightConeMap_mem_range_iff {n d : ℕ}
    (t : (Δ[1] : SSet.{u}) _⦋d⦌) (c : (Δ[n + 1] : SSet.{u}) _⦋d⦌) :
    (t, c) ∈ Set.range ((prismRightConeMap n).app (Opposite.op ⦋d⦌)) ↔
      ∀ i : Fin (d + 1), c i = Fin.last (n + 1) → t i = 1 := by
  constructor
  · rintro ⟨s, hs⟩ i hi
    have he := prismRightConeMap_last_time_one s i (by simpa only [hs] using hi)
    simpa only [hs] using he
  · exact prismRightConeMap_mem_range t c

end SerrePositivity.InfinityCategories
