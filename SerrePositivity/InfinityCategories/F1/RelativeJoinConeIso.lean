module

public import SerrePositivity.InfinityCategories.F1.PrismRightConePullback
public import SerrePositivity.InfinityCategories.F1.JoinLeftPullback

/-!
概要：最後の面に沿う relative join は元の relative join の右錐と同型。
方針：定義の pullback に右錐を取り、prism の右錐の pullback と縦に貼り合わせる。
規約：標準単体の最後の面に沿う場合を扱う。
使われ方：Kerodon Proposition 5.2.4.5、終域の次元を下げる帰納段階。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：relative join の右錐の二成分は大きい終域の定義の pullback を与える。
方針：join による pullback の保存を結合同型で移送し、底の pullback と貼り合わせる。
規約：f の終域は標準 n 単体。
使われ方：Kerodon Proposition 5.2.4.5、右錐の比較の同型性の証明。 -/
lemma relativeJoinCone_isPullback {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    IsPullback (relativeJoinConeFirst f) (relativeJoinConeSecond f)
      (joinMap (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]))
      (joinDiagonal Δ[n + 1]) := by
  have h := join_left_isPullback
    (IsPullback.of_hasPullback (joinMap f (𝟙 Δ[n])) (joinDiagonal Δ[n])) (Δ[0] : SSet.{u})
  have htop : IsPullback (relativeJoinConeFirst f)
      (joinMap (pullback.snd (joinMap f (𝟙 Δ[n])) (joinDiagonal Δ[n])) (𝟙 Δ[0]))
      (joinMap f (𝟙 Δ[n + 1])) (prismRightConeDiagonal n) := by
    apply h.of_iso (Iso.refl _) (rightConeJoinIso Δ[m] n) (Iso.refl _)
      (rightConeJoinIso Δ[n] n)
    · simpa only [Iso.refl_hom, Category.id_comp] using (relativeJoinConeFirst_factor f).symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · exact rightConeJoinIso_naturality f n
    · rfl
  have hp := htop.paste_vert (prismRightCone_isPullback n)
  rw [← relativeJoinConeSecond_factor f, ← joinMap_comp, Category.id_comp] at hp
  exact hp

/-- 概要：右錐の標準比較射は同型。
方針：二成分の pullback から得られる標準同型と比較射を射影で一致させる。
規約：同型は既存の標準比較射そのものについて述べる。
使われ方：Kerodon Proposition 5.2.4.5、最後の面への因子化による帰納。 -/
instance relativeJoinConeMap_isIso {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    IsIso (relativeJoinConeMap f) := by
  have he : relativeJoinConeMap f = (relativeJoinCone_isPullback f).isoPullback.hom := by
    apply pullback.hom_ext
    · rw [relativeJoinConeMap_fst, IsPullback.isoPullback_hom_fst]
    · rw [relativeJoinConeMap_snd, IsPullback.isoPullback_hom_snd]
  rw [he]
  infer_instance

/-- 概要：最後の面に沿う relative join と小さい終域の relative join の右錐の同型。
方針：標準比較射の同型性を束ねる。
規約：順方向は右錐から大きい終域の relative join。
使われ方：Kerodon Proposition 5.2.4.5、f(m)<n の場合の同定。 -/
noncomputable def relativeJoinConeIso {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    join (relativeJoin f (𝟙 Δ[n])) Δ[0] ≅
      relativeJoin (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]) :=
  asIso (relativeJoinConeMap f)

end SerrePositivity.InfinityCategories
