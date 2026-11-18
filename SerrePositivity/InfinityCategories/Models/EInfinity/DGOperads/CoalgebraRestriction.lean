module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Coalgebra
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CoComposition
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Morphism

/-!
模型。文献の定義との比較は後で
# オペラッド射に沿う余代数の制限

概要：Berger–Fresse §3.1 の余演算をオペラッド射の前合成で制限する。
方針：単位・自然性・部分合成保存を余演算の係数自然性へ適用する。
規約：余代数の底の複体とその射は変えない。
使われ方：Com 余代数の E 余代数化と、区間切断作用の TR に沿う制限に用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：Q-coalgebra を P → Q に沿って P-coalgebra へ制限する（BF §3.1）。
方針：全ての余演算の係数へオペラッド射を前合成する。
規約：底の複体と出力のテンソル冪は同じである。
使われ方：既存の余代数構造を E の余代数構造へ引き戻す。 -/
def restrictCoalgebraObj (f : P ⟶ Q) (X : Q.Coalgebra) : P.Coalgebra where
  carrier := X.carrier
  coaction n := (f.map.app (_root_.SerrePositivity.FiniteBijection.of n) ▷ X.carrier) ≫ X.coaction n
  equivariance n σ := by
    change (P.sequence.map _ ▷ X.carrier) ≫
      (f.map.app _ ▷ X.carrier) ≫ X.coaction n = _
    rw [← comp_whiskerRight_assoc, f.map.naturality, comp_whiskerRight,
      Category.assoc, X.equivariance]
    simp only [Category.assoc]
  unit_coaction := by
    change (P.unit ▷ X.carrier) ≫ (f.map.app _ ▷ X.carrier) ≫
      X.coaction 1 ≫ (oneIso X.carrier).hom = _
    rw [← comp_whiskerRight_assoc, f.unit]
    exact X.unit_coaction
  comp_coaction m n i := by
    change (P.comp m n i ▷ X.carrier) ≫
      (f.map.app _ ▷ X.carrier) ≫ X.coaction (m + n) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoComposition X.carrier (P.arity (m + 1)) (P.arity n) m n i
        ((f.map.app _ ▷ X.carrier) ≫ X.coaction (m + 1))
        ((f.map.app _ ▷ X.carrier) ≫ X.coaction n)
    rw [← comp_whiskerRight_assoc, f.comp, comp_whiskerRight, Category.assoc]
    have hX : (Q.comp m n i ▷ X.carrier) ≫ X.coaction (m + n) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoComposition X.carrier (Q.arity (m + 1)) (Q.arity n) m n i
          (X.coaction (m + 1)) (X.coaction n) := X.comp_coaction m n i
    rw [hX]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoComposition_coeff _ _ m n i _ _

/-- 概要：余代数の制限により射も制限できる（BF §3.1）。
方針：係数射と底の射をテンソルの交換則で入れ替え、元の保存則を使う。
規約：底の chain map は変えない。
使われ方：余代数の制限関手の射成分となる。 -/
def restrictCoalgebraMap (f : P ⟶ Q) {X Y : Q.Coalgebra} (g : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictCoalgebraObj f X ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictCoalgebraObj f Y where
  hom := g.hom
  comm n := by
    change (P.arity n ◁ g.hom) ≫ (f.map.app _ ▷ Y.carrier) ≫ Y.coaction n =
      ((f.map.app _ ▷ X.carrier) ≫ X.coaction n) ≫ _root_.SerrePositivity.TensorPowers.map g.hom n
    rw [whisker_exchange_assoc, Category.assoc]
    exact congrArg (fun h => (f.map.app (_root_.SerrePositivity.FiniteBijection.of n) ▷ X.carrier) ≫ h)
      (g.comm n)

/-- 概要：オペラッド射に沿う余代数の制限関手（BF §3.1）。
方針：制限した対象と同じ底の射を用いる。
規約：忘却後は複体の恒等関手と厳密に可換となる。
使われ方：TR に沿って区間の余代数構造と端点を制限する。 -/
def restrictCoalgebra (f : P ⟶ Q) : Q.Coalgebra ⥤ P.Coalgebra where
  obj := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictCoalgebraObj f
  map := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictCoalgebraMap f
  map_id X := by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraHom.ext; rfl
  map_comp g h := by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraHom.ext; rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
