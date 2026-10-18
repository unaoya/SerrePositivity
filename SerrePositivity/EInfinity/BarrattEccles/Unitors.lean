module

public import SerrePositivity.EInfinity.BarrattEccles.Unit

/-!
# コチェイン複体の単位子の元での公式

概要：Berger–Fresse §1.1.3 の部分合成の単位則で既存のテンソル単位子を評価する。
方針：次数ごとの単位子の逆写像を全テンソルの一つの斉次成分で表す。
規約：テンソル単位の0次の元1は singleObjXSelf の逆同型で指定する。
使われ方：単位則を単位子の逆写像との合成で検証する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：右単位子の逆は斉次元に単位の元1を右からテンソルする（Berger–Fresse §1.1.3）。
方針：全テンソルの単位子の成分公式と加群の右単位子の値を使う。
規約：全ての整数次数 r で成立する。
使われ方：部分合成の右単位則を一入力の元で検証する。 -/
lemma cochain_rightUnitor_inv_apply (P : Complex A) (r : ℤ) (x : P.X r) :
    (ρ_ P).inv.f r x =
      ιTensorObj P (𝟙_ (Complex A)) r 0 r (add_zero r)
        (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) := by
  change (HomologicalComplex.rightUnitor' P).inv r x = _
  rw [HomologicalComplex.rightUnitor'_inv]
  change ιTensorObj P (𝟙_ (Complex A)) r 0 r (add_zero r)
    (((P.X r) ◁ (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv)
      ((ρ_ (P.X r)).inv x)) = _
  rw [ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply]

/-- 概要：左単位子の逆は斉次元に単位の元1を左からテンソルする（Berger–Fresse §1.1.3）。
方針：全テンソルの単位子の成分公式と加群の左単位子の値を使う。
規約：全ての整数次数 r で成立する。
使われ方：部分合成の左単位則を一入力の元で検証する。 -/
lemma cochain_leftUnitor_inv_apply (P : Complex A) (r : ℤ) (x : P.X r) :
    (λ_ P).inv.f r x =
      ιTensorObj (𝟙_ (Complex A)) P 0 r r (zero_add r)
        ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) ⊗ₜ[A] x) := by
  change (HomologicalComplex.leftUnitor' P).inv r x = _
  rw [HomologicalComplex.leftUnitor'_inv]
  change ιTensorObj (𝟙_ (Complex A)) P 0 r r (zero_add r)
    (((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv ▷ (P.X r))
      ((λ_ (P.X r)).inv x)) = _
  rw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]

end SerrePositivity.EInfinity.BarrattEccles
