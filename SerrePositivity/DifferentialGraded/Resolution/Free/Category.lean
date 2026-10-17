module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Associativity
public import SerrePositivity.DifferentialGraded.Resolution.Free.EvaluationComposition
public import SerrePositivity.DifferentialGraded.Tensor.ObjectwiseKFlat

/-! # 複体値quiver上の主豊穣モデルによる自由dg圏

## 概要
複体値quiver上の主豊穣モデルによる自由dg圏。

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
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

/-- quiverと結び付けた自由dg圏の対象型。元のDのinstanceは変更しない。 -/
def Objects (_K : ComplexQuiver A D) : Type v := D

instance objectsSmall (K : ComplexQuiver A D) : Small.{u} (Objects A D K) :=
  inferInstanceAs (Small.{u} D)

instance dgCategory (K : ComplexQuiver A D) : DGCategory A (Objects A D K) where
  Hom X Y := homComplex A D K X Y
  id X := unitInclusion A D K X
  comp X Y Z := composition A D K X Y Z
  id_comp X Y := by
    change (λ_ (homComplex A D K X Y)).inv ≫
      (unitInclusion A D K X ▷ homComplex A D K X Y) ≫ composition A D K X X Y = _
    rw [composition_left_unit, Iso.inv_hom_id]
  comp_id X Y := by
    change (ρ_ (homComplex A D K X Y)).inv ≫
      (homComplex A D K X Y ◁ unitInclusion A D K Y) ≫ composition A D K X Y Y = _
    rw [composition_right_unit, Iso.inv_hom_id]
  assoc X Y Z T := by
    change (α_ (homComplex A D K X Y) (homComplex A D K Y Z) (homComplex A D K Z T)).inv ≫
      (composition A D K X Y Z ▷ homComplex A D K Z T) ≫ composition A D K X Z T = _
    rw [composition_assoc, Iso.inv_hom_id_assoc]

/-- 各辺がA上K-flatなら自由dg圏の全HomもK-flat。 -/
lemma homKFlat (K : ComplexQuiver A D) (hK : ∀ x y, complexKFlat A (K x y)) :
    localHomKFlat A (Objects A D K) := by
  intro x y
  exact homComplex_kFlat A D K hK x y

variable (E : Type w) [DGCategory A E]

/-- 対象写像と辺のchain mapから自由dg圏上のdg関手を構成する。 -/
def lift (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) : DGFunctor A (Objects A D K) E where
  obj X := o X
  map X Y := homEvaluation A D E K o f X Y
  map_id X := unitInclusion_homEvaluation A D E K o f X
  map_comp X Y Z := homEvaluation_composition A D E K o f X Y Z

lemma lift_edge (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) (x y : D) :
    edgeInclusion A D K x y ≫ (lift A D E K o f).map x y = f x y :=
  edgeInclusion_homEvaluation A D E K o f x y

end SerrePositivity.DifferentialGraded.FreeDGCategory
