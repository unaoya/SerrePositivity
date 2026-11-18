module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyCompositeHomotopy
public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.TernaryInput

/-!
# E 代数の実際の H⁰ の積の結合性

概要：BF §1・BM §1 の二つの部分合成から H⁰ の積の結合性を得る。
方針：同じ三入力演算を二つの位置の代入へホモトピーで移し、代表元で計算する。
規約：実際の非有界複体と元の homology 0 を使う。
使われ方：E2a-4 の H⁰ の可換環構造。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open _root_.SerrePositivity.HomologyZero

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power

/-- 概要：二項積の二つの括弧付けは実際の鎖ホモトピーで結ばれる（BF §1）。
方針：同じ三入力演算から先頭・第二位置への代入のホモトピーを合成する。
規約：Koszul テンソルの実際の結合子を含む。
使われ方：H⁰ の積の結合性。 -/
def homologyBinaryAssociativityHomotopy (X : (operad A).Algebra) :
    Homotopy ((homologyBinary X ▷ X.carrier) ≫ homologyBinary X)
      ((α_ X.carrier X.carrier X.carrier).hom ≫
        (X.carrier ◁ homologyBinary X) ≫ homologyBinary X) := by
  have hb : (λ_ (power X.carrier 2)).hom ≫ homologyOperation X 2 =
      (aritySection A 2 ▷ power X.carrier 2) ≫ X.action 2 := by
    simp only [homologyOperation, Iso.hom_inv_id_assoc]
  have hl := (homologyCompositionHomotopy X 1 2 0).compLeft (_root_.SerrePositivity.HomologyZero.ternaryInput X.carrier)
  have hr := (homologyCompositionHomotopy X 1 2 1).compLeft (_root_.SerrePositivity.HomologyZero.ternaryInput X.carrier)
  rw [← hb, _root_.SerrePositivity.HomologyZero.binaryAssociativityLeftInput] at hl
  rw [← hb, _root_.SerrePositivity.HomologyZero.binaryAssociativityRightInput] at hr
  simpa only [homologyBinary, Category.assoc] using hl.symm.trans hr

/-- 概要：E 代数の実際の H⁰ の積は結合的（BF §1、BM §1）。
方針：三元を単位からの射で表し、結合ホモトピーに共通の三入力を前合成する。
規約：元の H⁰ の双線形積について述べる。
使われ方：H⁰ の可換環構造の結合則。 -/
lemma homologyProduct_assoc (X : (operad A).Algebra) (x y z : X.carrier.homology 0) :
    homologyProduct X (homologyProduct X x y) z =
      homologyProduct X x (homologyProduct X y z) := by
  obtain ⟨f, rfl⟩ := _root_.SerrePositivity.HomologyZero.unitClass_surjective X.carrier x
  obtain ⟨g, rfl⟩ := _root_.SerrePositivity.HomologyZero.unitClass_surjective X.carrier y
  obtain ⟨h, rfl⟩ := _root_.SerrePositivity.HomologyZero.unitClass_surjective X.carrier z
  let μ := homologyBinary X
  change _root_.SerrePositivity.HomologyZero.pairingValue μ (_root_.SerrePositivity.HomologyZero.pairingValue μ (_root_.SerrePositivity.HomologyZero.unitClass X.carrier f) (_root_.SerrePositivity.HomologyZero.unitClass X.carrier g))
      (_root_.SerrePositivity.HomologyZero.unitClass X.carrier h) =
    _root_.SerrePositivity.HomologyZero.pairingValue μ (_root_.SerrePositivity.HomologyZero.unitClass X.carrier f)
      (_root_.SerrePositivity.HomologyZero.pairingValue μ (_root_.SerrePositivity.HomologyZero.unitClass X.carrier g) (_root_.SerrePositivity.HomologyZero.unitClass X.carrier h))
  simp only [_root_.SerrePositivity.HomologyZero.pairingValue_class]
  apply (_root_.SerrePositivity.HomologyZero.unitClass_eq_iff X.carrier _ _).mpr
  let t := (λ_ (𝟙_ (Complex A))).inv ≫
    (((λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ g)) ⊗ₘ h)
  have hl : _root_.SerrePositivity.HomologyZero.unitPairing μ (_root_.SerrePositivity.HomologyZero.unitPairing μ f g) h = t ≫ (μ ▷ X.carrier) ≫ μ := by
    change (λ_ (𝟙_ (Complex A))).inv ≫
      (((λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ g) ≫ μ) ⊗ₘ h) ≫ μ = _
    dsimp only [t]
    monoidal
  have hr : _root_.SerrePositivity.HomologyZero.unitPairing μ f (_root_.SerrePositivity.HomologyZero.unitPairing μ g h) =
      t ≫ (α_ X.carrier X.carrier X.carrier).hom ≫ (X.carrier ◁ μ) ≫ μ := by
    change (λ_ (𝟙_ (Complex A))).inv ≫
      (f ⊗ₘ ((λ_ (𝟙_ (Complex A))).inv ≫ (g ⊗ₘ h) ≫ μ)) ≫ μ = _
    dsimp only [t]
    monoidal
  exact ⟨(Homotopy.ofEq hl).trans
    (((homologyBinaryAssociativityHomotopy X).compLeft t).trans (Homotopy.ofEq hr.symm))⟩

end SerrePositivity.EInfinity.BarrattEccles
