module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicFaithful
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthPositive

/-!
概要：非原子的な実全鎖の原子分解に現れる任意の実原子の幅は、全体の幅より小さい。
方針：一段の道の実像は原子的であり、非原子的な道の指定原子の前後は一方が空でない。
規約：元の実射を添字にした自由な道と、その実合成関手を使う。
使われ方：Riehl–Verity Proposition 4.2.15の境界面の実原子分解、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの幅の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：長さ一の実原子的な道の実像は原子的。
方針：最初の生成射と長さ0の残りへ分け、空の道と実生成射の回収を使う。
規約：全次数・同じ二対象。使われ方：Riehl–Verity §4.2の非原子的な分解の長さの検収。 -/
lemma walkingAdjunctionAtomicPath_atomic_of_length_one {n : ℕ}
    {A B : WalkingAdjunctionAtomicVertex n} (p : Quiver.Path A B) (hp : p.length = 1) :
    WalkingAdjunctionLevelIsAtomic ((walkingAdjunctionAtomicPathFunctor n).map p) := by
  obtain ⟨C, e, q, hq, rfl⟩ := p.eq_toPath_comp_of_length_eq_succ (n := 0) hp
  have hCB := q.eq_of_length_zero hq
  subst B
  have hqnil := q.eq_nil_of_length_zero hq
  subst q
  change WalkingAdjunctionLevelIsAtomic
    ((walkingAdjunctionAtomicPathFunctor n).map e.toPath)
  rw [walkingAdjunctionAtomicPathFunctor_generator]
  exact e.property

/-- 概要：指定した実原子の前後へ実道を付けた合成の幅は、三つの幅の和。
方針：元の実道の合成を実全水平合成へ戻し、全水平合成の加法性を二回使う。
規約：空の道も含む。使われ方：Riehl–Verity §4.2の任意の実原子因子の幅の計算。 -/
lemma walkingAdjunctionAtomicFactor_width_sum {n : ℕ}
    {A B C D : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path A B) (e : B ⟶ C) (r : Quiver.Path C D) :
    walkingAdjunctionOrdinalWidth
      ((walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r))) =
      walkingAdjunctionOrdinalWidth ((walkingAdjunctionAtomicPathFunctor n).map q) +
        (walkingAdjunctionOrdinalWidth e.val +
          walkingAdjunctionOrdinalWidth ((walkingAdjunctionAtomicPathFunctor n).map r)) := by
  have h : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) =
      (walkingAdjunctionAtomicPathFunctor n).map q ≫
        (e.val ≫ (walkingAdjunctionAtomicPathFunctor n).map r) := by
    change (walkingAdjunctionAtomicPathFunctor n).map (q ≫ (e.toPath ≫ r)) = _
    rw [Functor.map_comp, Functor.map_comp, walkingAdjunctionAtomicPathFunctor_generator]
  have hq := walkingAdjunctionOrdinalWidth_horizontal A.level.point B.level.point D.level.point
    ((walkingAdjunctionAtomicPathFunctor n).map q)
    (e.val.prod' ((walkingAdjunctionAtomicPathFunctor n).map r) ⋙
      walkingAdjunctionHorizontal B.level.point C.level.point D.level.point)
  have he := walkingAdjunctionOrdinalWidth_horizontal B.level.point C.level.point D.level.point
    e.val ((walkingAdjunctionAtomicPathFunctor n).map r)
  exact (congrArg walkingAdjunctionOrdinalWidth h).trans
    (hq.trans (congrArg (fun t =>
      walkingAdjunctionOrdinalWidth ((walkingAdjunctionAtomicPathFunctor n).map q) + t) he))

/-- 概要：非原子的な実道の像に現れる任意の実原子の幅は、全体の実幅より真に小さい。
方針：前後の道が両方空なら一段の道となり原子的なので、少なくとも一方の実幅は正。
規約：指定因子を先頭に限定しない。使われ方：Riehl–Verity §4.2の全原子因子の厳密な境界。 -/
lemma walkingAdjunctionAtomicFactor_width_lt {n : ℕ}
    {A B C D : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path A B) (e : B ⟶ C) (r : Quiver.Path C D)
    (ha : ¬ WalkingAdjunctionLevelIsAtomic
      ((walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)))) :
    walkingAdjunctionOrdinalWidth e.val < walkingAdjunctionOrdinalWidth
      ((walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r))) := by
  have hl : (q.comp (e.toPath.comp r)).length ≠ 1 :=
    fun h => ha (walkingAdjunctionAtomicPath_atomic_of_length_one _ h)
  have hpos : 0 < q.length ∨ 0 < r.length := by
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hl
    omega
  have hw := walkingAdjunctionAtomicFactor_width_sum q e r
  rcases hpos with hq | hr
  · have hp := (walkingAdjunctionOrdinalWidth_pos_iff_size_pos _).mpr
      (walkingAdjunctionAtomicPathFunctor_size_pos q hq)
    omega
  · have hp := (walkingAdjunctionOrdinalWidth_pos_iff_size_pos _).mpr
      (walkingAdjunctionAtomicPathFunctor_size_pos r hr)
    omega

end SerrePositivity.InfinityCategories.HA.Monads
