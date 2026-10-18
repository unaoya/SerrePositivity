module

public import SerrePositivity.KST.Descent.NoetherianThickening
public import SerrePositivity.KST.Descent.ClosedPullbackAction
public import SerrePositivity.KST.Descent.DescentNaturality

/-!
# 冪零な基底変更と全次数の降下

## 概要
冪零 thickening に沿う実際の基底変更の前後で、指定された降下比較を移す。

## 方針
引き戻しの群作用と二つの冪零不変性を、同変正方形の比較に適用する。

## 規約
始域の Noether 性と前層の公理 (3) を明示する。閉中心の構造は変更しない。

## 使われ方
論文 補題 3.3・定理 3.1 の閉中心に対する帰納と冪零不変性の接続。
-/

@[expose] public section

universe u w t

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {X Y Z : FiniteTypeSchemes S} {G : Type*} [Group G]
variable (f : X ⟶ Y) (i : Z ⟶ Y)
variable (action : G →* Aut X) (over_base : ∀ g, (action g).asIso.hom ≫ f = f)

/-- 概要：基底上の作用を閉埋め込みによる基底変更へ移す（論文 §3）。
方針：基底と中心を自明作用として既存の引き戻し作用を使う。
規約：元の射 f と実際の引き戻しの第一射影を保持する。
使われ方：冪零な基底変更後の指定降下比較。 -/
noncomputable def closedBaseChangeAction [IsClosedImmersion i.hom.left] :
    G →* Aut (closedImmersionPullback f i) :=
  closedPullbackAction f i action 1 1 (fun g ↦ by simpa using over_base g)
    (fun _ ↦ by simp)

/-- 概要：基底変更後の作用は第二射影の基底上にある（論文 (3.7)）。
方針：第二射影の同変性と中心の自明作用を用いる。
規約：基底変更後の基底は Z である。
使われ方：PiDescent の作用に関する指定可換式。 -/
theorem closedBaseChangeAction_over_base [IsClosedImmersion i.hom.left] (g : G) :
    (closedBaseChangeAction f i action over_base g).asIso.hom ≫
      (closedImmersionSquare f i).f₁₃ = (closedImmersionSquare f i).f₁₃ := by
  exact (closedPullbackAction_snd f i action 1 1
    (fun g ↦ by simpa using over_base g) (fun _ ↦ by simp) g).trans
      (Category.comp_id _)

/-- 概要：冪零な基底変更の前後で全次数の降下は同値（論文 補題 3.3）。
方針：第一射影と基底の包含の冪零不変性を、実際の同変正方形に適用する。
規約：負次数と任意の係数を含む。有限群性はこの移行には不要。
使われ方：閉中心上の帰納仮定を非被約な幾何データと比較する。 -/
theorem Nilinvariant.piDescent_iff_thickening_baseChange {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient)
    [Nilinvariant S L] [IsNilpotentThickening i.hom.left] [IsNoetherian X.obj.left] :
    L.PiDescent f action over_base ↔
      L.PiDescent (closedImmersionSquare f i).f₁₃
        (closedBaseChangeAction f i action over_base)
        (closedBaseChangeAction_over_base f i action over_base) := by
  apply L.piDescent_iff_of_bijective_square f (closedImmersionSquare f i).f₁₃
    (closedImmersionSquare f i).f₁₂ i (closedImmersionSquare f i).fac
    action (closedBaseChangeAction f i action over_base) over_base
    (closedBaseChangeAction_over_base f i action over_base)
  · exact closedPullbackAction_fst f i action 1 1
      (fun g ↦ by simpa using over_base g) (fun _ ↦ by simp)
  · exact Nilinvariant.closedPullback_pullback_bijective L f i
  · exact Nilinvariant.pullback_bijective (S := S) (L := L) i

end SerrePositivity.KST.Descent
