module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ArrowInterpolationCocone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ArrowInterpolationCornerImage

/-!
概要：補間余錐の比較の切断と終点の計算。
方針：結合同型の切断公式と右因子の自然性を使う。
規約：空次数も含む切断表示。使われ方：全円柱比較の逆の構成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 二重余錐を潰した単体の切断は、元の内側の切断そのもの。 -/
lemma arrowInterpolationConeFold_cut {A : SSet.{u}} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u})) Δ[0] n) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationConeFold A).app (Opposite.op ⦋n⦌) s).1.val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinEquiv A Δ[0] s.1.val s.2.1).1.val := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinEquiv A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] Δ[0]) (n + 1)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinAssociatorEquiv A Δ[0] Δ[0] (n + 1) s)).1.val = _
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinEquiv A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] Δ[0]) (n + 1)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinEquiv A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] Δ[0]) (n + 1)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugReassociationEquiv A Δ[0] Δ[0] (n + 1)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0]) Δ[0] (n + 1) s)))).1.val = _
  rw [Equiv.apply_symm_apply]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugReassociation_cut A Δ[0] Δ[0] (n + 1) s

/-- 折り畳みの最後の点は、元の余錐の同じ頂点。 -/
lemma arrowInterpolationConeFold_inr (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u})) Δ[0] ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationConeFold A = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationConeFold, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinAssociator_inr,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, ← Category.assoc]
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 0 = 𝟙 Δ[0] :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he, Category.id_comp]

/-- 区間の右余錐の最後の点は区間の終点。 -/
lemma arrowInterpolationInterval_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] : SSet.{u}) Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 1 =
      SSet.const (stdSimplex.obj₀Equiv.symm 1) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation_app_of_ge 1 n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inr s) i (Nat.zero_le _)

/-- 比較余錐の頂点は、全円柱の新しい終端頂点そのもの。 -/
lemma arrowInterpolationCocone_inr (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCorner A) (Δ[0] : SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone A = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ SSet.ι₁ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone, Category.assoc, lift_fst, SSet.ι₁_fst,
      Category.comp_id]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp,
      arrowInterpolationConeFold_inr]
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone, Category.assoc, lift_snd, SSet.ι₁_snd]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp, arrowInterpolationInterval_inr]
    exact (SSet.comp_const _ _).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
