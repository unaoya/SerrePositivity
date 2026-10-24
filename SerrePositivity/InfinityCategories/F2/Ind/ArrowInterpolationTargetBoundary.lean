module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationInverseBoundary
public import SerrePositivity.InfinityCategories.Core.JoinAssociatorMiddle
/-!
概要：補間全円柱の終点面は、同じ補間領域の旧終点族の余錐に厳密に一致する。
方針：全円柱同型の二座標と join の結合同型を計算する。
規約：全パラメーターで元の全射を保持する。
使われ方：終点評価下の指定変換を補間余錐へ追加する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：補った標準単体上でも最後の頂点の定値性を保つ。
方針：空次数を分ける。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma join_stdAug_constant_last {A : SSet.{u}} (n r : ℕ) (a : Join.augObj A r) (i : Fin r) :
    Join.stdAugEquiv n r (Join.augHom
      (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n)) : A ⟶ Δ[n]) r a) i = Fin.last n := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r => rfl
/-- 概要：元の旧終点族の補間領域への包含。
方針：円柱の一端点を使う。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
def arrowInterpolationTargetInclusion (A : SSet.{u}) : A ⟶ arrowInterpolationCorner A :=
  SSet.ι₁ ≫ pushout.inl SSet.ι₀ (joinInl A (Δ[0] : SSet.{u}))
/-- 概要：旧終点族の全円柱への像は元の終点面。
方針：包含と端点を合成する。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma arrowInterpolationTargetInclusion_comp (A : SSet.{u}) :
    arrowInterpolationTargetInclusion A ≫ arrowInterpolationCornerInclusion A =
      joinInl A Δ[0] ≫ SSet.ι₁ := by
  rw [arrowInterpolationTargetInclusion, Category.assoc, arrowInterpolationCornerInclusion_old]
  exact (SSet.ι₁_comp (joinInl A (Δ[0] : SSet.{u}))).symm
/-- 概要：旧終点族の余錐は元の全終点面を回収する。
方針：二座標で検査する。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma arrowInterpolationCocone_target (A : SSet.{u}) :
    joinMap (arrowInterpolationTargetInclusion A) (𝟙 (Δ[0] : SSet.{u})) ≫
      (arrowInterpolationCoconeIso A).hom = SSet.ι₁ := by
  change joinMap _ _ ≫ arrowInterpolationCocone A = _
  apply CartesianMonoidalCategory.hom_ext
  · simp only [arrowInterpolationCocone, Category.assoc, lift_fst]
    rw [← Category.assoc, ← joinMap_comp, Category.comp_id]
    have h : arrowInterpolationTargetInclusion A ≫ arrowInterpolationCornerInclusion A ≫
        fst (join A Δ[0]) Δ[1] = joinInl A Δ[0] := by
      rw [← Category.assoc, arrowInterpolationTargetInclusion_comp, Category.assoc,
        SSet.ι₁_fst, Category.comp_id]
    rw [h]
    have hfold : joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ stableLastJoinEvaluation 0 = 𝟙 _ :=
      stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [arrowInterpolationConeFold, ← Category.assoc, stableJoinAssociator_middle,
      ← joinMap_comp, Category.id_comp, hfold, joinMap_id]
    exact (SSet.ι₁_fst (join A (Δ[0] : SSet.{u}))).symm
  · simp only [arrowInterpolationCocone, Category.assoc, lift_snd]
    rw [← Category.assoc, ← joinMap_comp, Category.comp_id]
    have h : arrowInterpolationTargetInclusion A ≫ arrowInterpolationCornerInclusion A ≫
        snd (join A Δ[0]) Δ[1] = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
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
    change ((stableLastJoinEvaluation 1).app _
      ((joinMap (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) : A ⟶ Δ[1])
        (𝟙 (Δ[0] : SSet.{u}))).app _ s)) i =
      ((SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) : join A Δ[0] ⟶ Δ[1]).app _ s) i
    by_cases hi : i.val < s.1.val
    · rw [stableLastJoinEvaluation_app_of_lt 1 n _ i hi]
      change Join.stdAugEquiv 1 s.1.val (Join.augHom
        (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last 1)) : A ⟶ Δ[1])
          s.1.val s.2.1) ⟨i.val, hi⟩ = Fin.last 1
      exact join_stdAug_constant_last _ _ _ _
    · rw [stableLastJoinEvaluation_app_of_ge 1 n _ i (Nat.le_of_not_lt hi)]
      rfl
/-- 概要：全円柱の逆比較も同じ終点面を厳密に回収する。
方針：同型を消去する。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma arrowInterpolationCoconeIso_inv_target (A : SSet.{u}) :
    SSet.ι₁ ≫ (arrowInterpolationCoconeIso A).inv =
      joinMap (arrowInterpolationTargetInclusion A) (𝟙 (Δ[0] : SSet.{u})) := by
  apply (cancel_mono (arrowInterpolationCoconeIso A).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (arrowInterpolationCocone_target A).symm
/-- 概要：元の旧終点族の包含は単射。
方針：全円柱への像で反映する。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
instance arrowInterpolationTargetInclusion_mono (A : SSet.{u}) :
    Mono (arrowInterpolationTargetInclusion A) :=
  mono_of_mono_fac (arrowInterpolationTargetInclusion_comp A)
end SerrePositivity.InfinityCategories.F2.Ind
