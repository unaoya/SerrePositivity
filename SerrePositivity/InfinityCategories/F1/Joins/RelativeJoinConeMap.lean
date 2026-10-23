module

public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinConeFirst
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinConeSecond

/-!
概要：小さい終域の relative join の右錐から、大きい終域の relative join への比較。
方針：両成分の可換性を両因子の頂点で検査して引き戻しへ持ち上げる。
規約：ここでは標準比較の構成と単射性を示し、全射性は別に検証する。
使われ方：Kerodon Proposition 5.2.4.5、終域の次元を下げる右錐の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右錐の二成分は大きい終域の relative join の引き戻しの条件を満たす。
方針：元の因子では底の変更の可換性、新しい頂点では prism の終端の式を使う。
規約：標的の通常の join を標準単体と同定し、両因子への制限で等式を検査する。
使われ方：Kerodon Proposition 5.2.4.5、右錐の比較の引き戻しへの持ち上げ。 -/
lemma relativeJoinCone_condition {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    relativeJoinConeFirst f ≫ joinMap (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]) =
      relativeJoinConeSecond f ≫ joinDiagonal Δ[n + 1] := by
  let b := relativeJoinBaseMap f (stdSimplex.δ (Fin.last (n + 1)))
  have hF : joinInl (relativeJoin f (𝟙 Δ[n])) Δ[0] ≫ relativeJoinConeFirst f =
      b ≫ pullback.fst (joinMap (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]))
        (joinDiagonal Δ[n + 1]) :=
    (relativeJoinConeFirst_inl f).trans (relativeJoinBaseMap_fst f _).symm
  have hS : joinInl (relativeJoin f (𝟙 Δ[n])) Δ[0] ≫ relativeJoinConeSecond f =
      b ≫ pullback.snd (joinMap (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]))
        (joinDiagonal Δ[n + 1]) :=
    (relativeJoinConeSecond_inl f).trans (relativeJoinBaseMap_snd f _).symm
  have hL : joinInl (relativeJoin f (𝟙 Δ[n])) Δ[0] ≫
      (relativeJoinConeFirst f ≫ joinMap (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1])) =
      joinInl (relativeJoin f (𝟙 Δ[n])) Δ[0] ≫
        (relativeJoinConeSecond f ≫ joinDiagonal Δ[n + 1]) := by
    rw [← Category.assoc, hF, Category.assoc, pullback.condition, ← Category.assoc, ← hS,
      Category.assoc]
  have hR : joinInr (relativeJoin f (𝟙 Δ[n])) Δ[0] ≫
      (relativeJoinConeFirst f ≫ joinMap (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1])) =
      joinInr (relativeJoin f (𝟙 Δ[n])) Δ[0] ≫
        (relativeJoinConeSecond f ≫ joinDiagonal Δ[n + 1]) := by
    rw [← Category.assoc, relativeJoinConeFirst_inr, Category.assoc, joinInr_joinMap,
      Category.id_comp, ← prismEndpoint_one_joinDiagonal, ← Category.assoc,
      ← relativeJoinConeSecond_inr, Category.assoc]
  apply (cancel_mono (joinStdSimplexIso.{u} (n + 1) (n + 1)).hom).1
  apply relativeJoinCone_hom_ext_stdSimplex
  · simpa only [Category.assoc] using congrArg
      (fun k : relativeJoin f (𝟙 Δ[n]) ⟶ join (Δ[n + 1] : SSet.{u}) Δ[n + 1] ↦
        k ≫ (joinStdSimplexIso (n + 1) (n + 1)).hom) hL
  · simpa only [Category.assoc] using congrArg
      (fun k : (Δ[0] : SSet.{u}) ⟶ join (Δ[n + 1] : SSet.{u}) Δ[n + 1] ↦
        k ≫ (joinStdSimplexIso (n + 1) (n + 1)).hom) hR

/-- 概要：小さい終域の relative join の右錐から大きい終域の relative join への標準比較射。
方針：通常の join の成分と底の区間付き係数の成分を引き戻しへ持ち上げる。
規約：新しい頂点は右因子の最後の頂点に写る。
使われ方：Kerodon Proposition 5.2.4.5、f(m)<n の場合の右錐による比較。 -/
noncomputable def relativeJoinConeMap {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    join (relativeJoin f (𝟙 Δ[n])) Δ[0] ⟶
      relativeJoin (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]) :=
  pullback.lift (relativeJoinConeFirst f) (relativeJoinConeSecond f) (relativeJoinCone_condition f)

/-- 概要：右錐の比較の第一射影は指定した通常の join への射。
方針：引き戻しの第一射影の計算則を使う。
規約：底は標準 n+1 単体。
使われ方：Kerodon Proposition 5.2.4.5、右錐の比較の単射性と全射性の検査。 -/
lemma relativeJoinConeMap_fst {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    relativeJoinConeMap f ≫
        pullback.fst (joinMap (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]))
          (joinDiagonal Δ[n + 1]) = relativeJoinConeFirst f := pullback.lift_fst _ _ _

/-- 概要：右錐の比較の第二射影は指定した底の区間付き係数の射。
方針：引き戻しの第二射影の計算則を使う。
規約：時刻は新しい頂点で一になる。
使われ方：Kerodon Proposition 5.2.4.5、底上の比較の計算。 -/
lemma relativeJoinConeMap_snd {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    relativeJoinConeMap f ≫
        pullback.snd (joinMap (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]))
          (joinDiagonal Δ[n + 1]) = relativeJoinConeSecond f := pullback.lift_snd _ _ _

/-- 概要：右錐からの比較射は単射。
方針：第一射影との合成が単射であることを使う。
規約：同型性のうち全射性はここからは主張しない。
使われ方：Kerodon Proposition 5.2.4.5、右錐の比較を部分複体として扱う段階。 -/
instance relativeJoinConeMap_mono {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    Mono (relativeJoinConeMap f) := mono_of_mono_fac (relativeJoinConeMap_fst f)

end SerrePositivity.InfinityCategories
