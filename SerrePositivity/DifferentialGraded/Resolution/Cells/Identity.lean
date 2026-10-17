module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.CompositionComparison
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalUnits
public import SerrePositivity.DifferentialGraded.Complexes.UnitorCochainNaturality

/-! # cell付加の最終Hom合成：Identity

## 概要
cell付加の最終Hom合成：Identity。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 元の恒等射を最終Homへ入れた閉次数0の単位。 -/
def attachedIdentity (x : D) : 𝟙_ (Complex A) ⟶ C.attachedHom A D I x x :=
  eId (Complex A) x ≫ C.originalHomInclusion A D I x x

lemma attachedIdentity_f (x : D) (n : ℤ) :
    (C.attachedIdentity A D I x).f n = (C.internalIdentity A D I x).f n := rfl

lemma attachedComposition_left_unit (x y : D) :
    (λ_ (C.attachedHom A D I x y)).inv ≫ C.attachedIdentity A D I x ▷ C.attachedHom A D I x y ≫
      C.attachedComposition A D I x x y = 𝟙 _ := by
  apply chain_ext_apply
  intro n a
  simp only [chain_comp_apply]
  rw [complexLeftUnitor_inv_apply, whiskerRight_apply, attachedComposition_f, attachedIdentity_f]
  have h := congrArg (fun f : C.internalHom A D I x y ⟶ C.internalHom A D I x y => f.f n a)
    (C.internalComposition_left_unit A D I x y)
  change (C.internalComposition A D I x x y).f n
    ((C.internalIdentity A D I x ▷ C.internalHom A D I x y).f n
      ((λ_ (C.internalHom A D I x y)).inv.f n a)) = a at h
  rw [complexLeftUnitor_inv_apply, whiskerRight_apply] at h
  exact h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
