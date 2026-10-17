module
public import SerrePositivity.DifferentialGraded.Resolution.Free.PrefixAssociativity
public import SerrePositivity.DifferentialGraded.Complexes.TensorCarryAssociativity
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightTwoCoproductExt

/-! # 自由path直和の連結の結合則

## 概要
自由path直和の連結の結合則。

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
universe u v
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

lemma appendWord_assoc (K : ComplexQuiver A D) (w : List D) (x y z t : D) :
    (appendWord A D K w x y z ▷ homComplex A D K z t) ≫ composition A D K x z t =
      (α_ (wordTensor A D K w x y) (homComplex A D K y z) (homComplex A D K z t)).hom ≫
        wordTensor A D K w x y ◁ composition A D K y z t ≫ appendWord A D K w x y t := by
  induction w generalizing x with
  | nil => exact composition_edgePrefix A D K x y z t
  | cons b w ih =>
    have hk := tensorCarry_assoc (K x b) (wordTensor A D K w b y)
      (homComplex A D K y z) (homComplex A D K z t) (homComplex A D K b z)
      (homComplex A D K b t) (homComplex A D K y t)
      (appendWord A D K w b y z) (composition A D K b z t)
      (composition A D K y z t) (appendWord A D K w b y t) (ih b)
    have hp := congrArg (fun k => k ≫ edgePrefix A D K x b t) hk
    rw [appendWord_cons]
    simp only [comp_whiskerRight, Category.assoc]
    rw [composition_edgePrefix]
    simpa only [appendWord_cons, wordTensor, whiskerLeft_comp, comp_whiskerRight,
      Category.assoc] using hp

lemma appendPath_assoc (K : ComplexQuiver A D) {x y : D} (p : PathIndex D x y) (z t : D) :
    (appendPath A D K p z ▷ homComplex A D K z t) ≫ composition A D K x z t =
      (α_ (pathTensor A D K p) (homComplex A D K y z) (homComplex A D K z t)).hom ≫
        pathTensor A D K p ◁ composition A D K y z t ≫ appendPath A D K p t := by
  cases p with
  | inl h =>
    rcases h with ⟨h⟩
    subst y
    rw [appendPath_unit, appendPath_unit]
    change ((λ_ (homComplex A D K x z)).hom ▷ homComplex A D K z t) ≫
        composition A D K x z t =
      (α_ (𝟙_ (Complex A)) (homComplex A D K x z) (homComplex A D K z t)).hom ≫
        𝟙_ (Complex A) ◁ composition A D K x z t ≫ (λ_ (homComplex A D K x t)).hom
    rw [leftUnitor_naturality, ← Category.assoc, leftUnitor_tensor_hom'', tensorHom_id]
  | inr w => exact appendWord_assoc A D K w x y z t

lemma composition_assoc (K : ComplexQuiver A D) (x y z t : D) :
    (composition A D K x y z ▷ homComplex A D K z t) ≫ composition A D K x z t =
      (α_ (homComplex A D K x y) (homComplex A D K y z) (homComplex A D K z t)).hom ≫
        homComplex A D K x y ◁ composition A D K y z t ≫ composition A D K x y t := by
  apply tensorRightTwoCoproduct_hom_ext (pathTensor A D K (x := x) (y := y))
    (homComplex A D K y z) (homComplex A D K z t) (homComplex A D K x t)
  intro p
  change ((pathInclusion A D K x y p ▷ homComplex A D K y z) ▷ homComplex A D K z t) ≫
      (composition A D K x y z ▷ homComplex A D K z t) ≫ composition A D K x z t = _
  rw [← comp_whiskerRight_assoc, composition_left_inclusion,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  change (appendPath A D K p z ▷ homComplex A D K z t) ≫ composition A D K x z t =
    (α_ (pathTensor A D K p) (homComplex A D K y z) (homComplex A D K z t)).hom ≫
      pathTensor A D K p ◁ composition A D K y z t ≫
        (pathInclusion A D K x y p ▷ homComplex A D K y t) ≫ composition A D K x y t
  rw [composition_left_inclusion]
  exact appendPath_assoc A D K p z t

end SerrePositivity.DifferentialGraded.FreeDGCategory
