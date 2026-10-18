module

public import SerrePositivity.KST.Descent.NoetherianReduction
public import SerrePositivity.KST.Descent.ClosedImmersionSquare
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Noether な終域への全射閉埋め込み

## 概要
点全射な閉埋め込みの冪零性と、Noether な対象への底変換後の冪零性を証明する。

## 方針
核の台から核が nilradical に含まれることを示し、その大域的な冪零指数を使う。

## 規約
終域の Noether 性を明示する。一般の底変換安定性の代用とはしない。

## 使われ方
論文 補題 3.3・定理 3.1 の閉中心上で公理 (3) を適用するための幾何条件。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：Noether な終域への全射閉埋め込みは冪零 thickening（論文 補題 3.3）。
方針：核を nilradical に含め、nilradical の冪零性を移す。
規約：点全射性に加えて閉埋め込みと終域の Noether 性を要求する。
使われ方：中心への底変換後の冪零不変性の適用。 -/
theorem isNilpotentThickening_of_surjective_of_noetherian {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] [Surjective f] [IsNoetherian Y] :
    IsNilpotentThickening f := by
  have hs : f.ker.support = ⊤ := by
    apply SetLike.coe_injective
    rw [Scheme.Hom.support_ker, Set.range_eq_univ.mpr f.surjective]
    simp
  have hle : f.ker ≤ Y.nilradical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_top]
    exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp (by rw [hs])
  obtain ⟨n, hn⟩ := noetherian_nilradical_isNilpotent Y
  exact ⟨⟨n, le_bot_iff.mp ((pow_le_pow_left' hle n).trans_eq hn)⟩⟩

/-- 概要：Noether な対象への冪零 thickening の底変換も冪零（論文 §3）。
方針：閉埋め込みと点全射性の底変換安定性を用い、上の核の判定を適用する。
規約：底変換する射の始域に Noether 性を要求する。
使われ方：非被約な閉中心を保持したまま公理 (3) を適用する。 -/
theorem nilpotentThickening_pullback_fst {X Y Z : Scheme.{u}}
    (f : X ⟶ Z) (i : Y ⟶ Z) [IsNilpotentThickening i] [IsNoetherian X] :
    IsNilpotentThickening (pullback.fst f i) := by
  have : Surjective i := nilpotentThickening_surjective i
  exact isNilpotentThickening_of_surjective_of_noetherian (pullback.fst f i)

/-- 概要：有限型の圏内の閉中心の底変換で公理 (3) が適用できる（論文 補題 3.3）。
方針：実際のスキームの第一射影の冪零性を確認して前層の不変性を使う。
規約：中心は被約化せず、元の閉埋め込みの引き戻しを使う。
使われ方：任意の係数・整数次数で中心上の比較を移す。 -/
theorem Nilinvariant.closedPullback_pullback_bijective {S : Scheme.{u}}
    {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient)
    [Nilinvariant S L] {X Y Z : FiniteTypeSchemes S}
    (f : X ⟶ Z) (i : Y ⟶ Z) [IsNilpotentThickening i.hom.left]
    [IsNoetherian X.obj.left] (H : Coefficient) (n : ℤ) :
    Function.Bijective (L.pullback H n (closedImmersionSquare f i).f₁₂) := by
  have : IsNilpotentThickening (closedImmersionSquare f i).f₁₂.hom.left :=
    nilpotentThickening_pullback_fst f.hom.left i.hom.left
  exact Nilinvariant.pullback_bijective (S := S) (L := L)
    (closedImmersionSquare f i).f₁₂ H n

end SerrePositivity.KST.Descent
