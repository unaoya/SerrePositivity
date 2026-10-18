module

public import SerrePositivity.KST.Descent.FiniteTypeCoproducts
public import SerrePositivity.KST.Descent.LocalRankIsomorphisms

/-!
# 有限非交和の引き戻し成分と局所 rank

## 概要
有限非交和の任意の射による引き戻し成分は元の対象を非交和に分解し、各成分の正 rank 作用は可逆となる。

## 方針
有限非交和の普遍的余極限性を使い、その反対圏の有限積保存で成分の可逆性を反映する。

## 規約
引き戻す射は任意でよく、Čech の全座標を独立に分解する必要はない。

## 使われ方
論文 補題 3.2 の有限自由 chart の和への Čech の零番目の射影による rank の貼り合わせ。
-/

@[expose] public section

noncomputable section

universe u v w t

open CategoryTheory CategoryTheory.Limits CategoryTheory.Linear Opposite

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasPullbacks C] [FinitaryPreExtensive C]
  {I : Type w} [Finite I] (X : I → C) {T : C} (q : T ⟶ ∐ X)

/-- 概要：有限非交和を引き戻した成分は元の対象の実際の非交和（補題 3.2）。
方針：標準の非交和の普遍的余極限性を任意の射の引き戻しへ適用する。
規約：添字の universe を固定しない。使われ方：Čech の零番目の座標で各 chart へ分解する。 -/
def finiteCoproductPullbackIsColimit :
    IsColimit (Cofan.mk T (fun i : I ↦ pullback.fst q (Sigma.ι X i))) := by
  have hau := FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct X)
  apply Nonempty.some
  refine hau.nonempty_isColimit_of_pullbackCone_left _ (𝟙 _) _ _ (fun i ↦ ?_)
    (PullbackCone.mk (𝟙 _) q (by simp)) (IsPullback.id_horiz q).isLimit _ (Iso.refl _)
    (by simp) (by simp) (by simp [pullback.condition])
  exact pullback.isLimit _ _

omit [HasPullbacks C] in
/-- 概要：非交和の引き戻し成分での異なる正 rank は元の対象で可逆（補題 3.2）。
方針：実際の引き戻し成分の非交和を反対圏の有限積とし、自然な作用の同型性を反映する。
規約：rank は成分ごとに異なってよい。使われ方：有限自由 chart 上の rank 公式の合成の検査。 -/
theorem naturalEndomorphism_isIso_of_rankOnPullbackComponents
    {V : Type*} [Category* V] [Preadditive V] [Linear ℚ V]
    (F : Cᵒᵖ ⥤ V) [PreservesFiniteProducts F] (a : F ⟶ F)
    (rank : I → ℕ) (positive : ∀ i, 0 < rank i)
    (hlocal : ∀ i, a.app (op (pullback q (Sigma.ι X i))) =
      (rank i : ℚ) • 𝟙 (F.obj (op (pullback q (Sigma.ι X i))))) :
    IsIso (a.app (op T)) :=
  naturalEndomorphism_isIso_of_positiveRanks
    (Cofan.IsColimit.op (finiteCoproductPullbackIsColimit X q)) a
    (fun i : Discrete I ↦ rank i.as) (fun i ↦ positive i.as) (fun i ↦ hlocal i.as)

end SerrePositivity.KST.Descent
