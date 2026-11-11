module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ArrowInterpolationInverseBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinAssociatorMiddle
/-!
概要：補間全円柱の終点面は、同じ補間領域の旧終点族の余錐に厳密に一致する。
方針：全円柱同型の二座標と join の結合同型を計算する。
規約：全パラメーターで元の全射を保持する。
使われ方：終点評価下の指定変換を補間余錐へ追加する。

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
/-- 概要：補った標準単体上でも最後の頂点の定値性を保つ。
方針：空次数を分ける。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma join_stdAug_constant_last {A : SSet.{u}} (n r : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A r) (i : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom
      (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n)) : A ⟶ Δ[n]) r a) i = Fin.last n := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r => rfl
/-- 概要：元の旧終点族の補間領域への包含。
方針：円柱の一端点を使う。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
def arrowInterpolationTargetInclusion (A : SSet.{u}) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCorner A :=
  SSet.ι₁ ≫ pushout.inl SSet.ι₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u}))
/-- 概要：旧終点族の全円柱への像は元の終点面。
方針：包含と端点を合成する。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma arrowInterpolationTargetInclusion_comp (A : SSet.{u}) :
    arrowInterpolationTargetInclusion A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ≫ SSet.ι₁ := by
  rw [arrowInterpolationTargetInclusion, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion_old]
  exact (SSet.ι₁_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u}))).symm
/-- 概要：旧終点族の余錐は元の全終点面を回収する。
方針：二座標で検査する。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma arrowInterpolationCocone_target (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (arrowInterpolationTargetInclusion A) (𝟙 (Δ[0] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCoconeIso A).hom = SSet.ι₁ := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone A = _
  apply CartesianMonoidalCategory.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone, Category.assoc, lift_fst]
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id]
    have h : arrowInterpolationTargetInclusion A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion A ≫
        fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0]) Δ[1] = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] := by
      rw [← Category.assoc, arrowInterpolationTargetInclusion_comp, Category.assoc,
        SSet.ι₁_fst, Category.comp_id]
    rw [h]
    have hfold : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 0 = 𝟙 _ :=
      stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationConeFold, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinAssociator_middle,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, hfold, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id]
    exact (SSet.ι₁_fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}))).symm
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCocone, Category.assoc, lift_snd]
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id]
    have h : arrowInterpolationTargetInclusion A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion A ≫
        snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0]) Δ[1] = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
      rw [← Category.assoc, arrowInterpolationTargetInclusion_comp, Category.assoc,
        SSet.ι₁_snd, SSet.comp_const]
    rw [h]
    rw [SSet.ι₁_snd]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    apply stdSimplex.ext
    intro i
    change ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 1).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) : A ⟶ Δ[1])
        (𝟙 (Δ[0] : SSet.{u}))).app _ s)) i =
      ((SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0] ⟶ Δ[1]).app _ s) i
    by_cases hi : i.val < s.1.val
    · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation_app_of_lt 1 n _ i hi]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 1 s.1.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom
        (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last 1)) : A ⟶ Δ[1])
          s.1.val s.2.1) ⟨i.val, hi⟩ = Fin.last 1
      exact join_stdAug_constant_last _ _ _ _
    · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation_app_of_ge 1 n _ i (Nat.le_of_not_lt hi)]
      rfl
/-- 概要：全円柱の逆比較も同じ終点面を厳密に回収する。
方針：同型を消去する。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma arrowInterpolationCoconeIso_inv_target (A : SSet.{u}) :
    SSet.ι₁ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCoconeIso A).inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (arrowInterpolationTargetInclusion A) (𝟙 (Δ[0] : SSet.{u})) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCoconeIso A).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (arrowInterpolationCocone_target A).symm
/-- 概要：元の旧終点族の包含は単射。
方針：全円柱への像で反映する。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
instance arrowInterpolationTargetInclusion_mono (A : SSet.{u}) :
    Mono (arrowInterpolationTargetInclusion A) :=
  mono_of_mono_fac (arrowInterpolationTargetInclusion_comp A)
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
