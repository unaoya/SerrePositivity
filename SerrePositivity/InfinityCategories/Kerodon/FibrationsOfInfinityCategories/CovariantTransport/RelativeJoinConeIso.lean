module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.PrismRightConePullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinLeftPullback

/-!
概要：最後の面に沿う relative join は元の relative join の右錐と同型。
方針：定義の pullback に右錐を取り、prism の右錐の pullback と縦に貼り合わせる。
規約：標準単体の最後の面に沿う場合を扱う。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、終域の次元を下げる帰納段階。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：relative join の右錐の二成分は大きい終域の定義の pullback を与える。
方針：join による pullback の保存を結合同型で移送し、底の pullback と貼り合わせる。
規約：f の終域は標準 n 単体。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、右錐の比較の同型性の証明。 -/
lemma relativeJoinCone_isPullback {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeFirst f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeSecond f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n + 1]) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_left_isPullback
    (IsPullback.of_hasPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[n])) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n])) (Δ[0] : SSet.{u})
  have htop : IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeFirst f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[n])) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n])) (𝟙 Δ[0]))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[n + 1])) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeDiagonal n) := by
    apply h.of_iso (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.rightConeJoinIso Δ[m] n) (Iso.refl _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.rightConeJoinIso Δ[n] n)
    · simpa only [Iso.refl_hom, Category.id_comp] using (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeFirst_factor f).symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.rightConeJoinIso_naturality f n
    · rfl
  have hp := htop.paste_vert (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightCone_isPullback n)
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeSecond_factor f, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp] at hp
  exact hp

/-- 概要：右錐の標準比較射は同型。
方針：二成分の pullback から得られる標準同型と比較射を射影で一致させる。
規約：同型は既存の標準比較射そのものについて述べる。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、最後の面への因子化による帰納。 -/
instance relativeJoinConeMap_isIso {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeMap f) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeMap f = (relativeJoinCone_isPullback f).isoPullback.hom := by
    apply pullback.hom_ext
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeMap_fst, IsPullback.isoPullback_hom_fst]
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeMap_snd, IsPullback.isoPullback_hom_snd]
  rw [he]
  infer_instance

/-- 概要：最後の面に沿う relative join と小さい終域の relative join の右錐の同型。
方針：標準比較射の同型性を束ねる。
規約：順方向は右錐から大きい終域の relative join。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、f(m)<n の場合の同定。 -/
noncomputable def relativeJoinConeIso {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Δ[n])) Δ[0] ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]) :=
  asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeMap f)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
