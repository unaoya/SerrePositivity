module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyCommutativity
public import SerrePositivity.EInfinity.BarrattEccles.HomologyCompositeHomotopy
public import SerrePositivity.EInfinity.BarrattEccles.HomologyUnary
public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.NullaryInput

/-!
# E 代数の実際の H⁰ の積の単位則

概要：BF §1・BM §1 の nullary 部分合成から H⁰ の積の左右の単位則を得る。
方針：一入力演算との比較、零入力の代入、H⁰ の代表元の公式を使う。
規約：実際の homologyOne と homologyProduct について述べる。
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

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] TensorPowers.power

/-- 概要：選んだ零入力の左代入は二項積の左単位ホモトピーを与える（BF §1）。
方針：部分合成ホモトピーを一入力の恒等ホモトピーと比較する。
規約：零入力の作用と実際の二項複体射を使う。
使われ方：H⁰ の左単位則。 -/
def homologyBinaryLeftUnitHomotopy (X : (operad A).Algebra) :
    Homotopy ((λ_ X.carrier).inv ≫ (homologyOperation X 0 ▷ X.carrier) ≫ homologyBinary X)
      (𝟙 X.carrier) := by
  have hb : (λ_ (𝟙_ (Complex A))).hom ≫ homologyOperation X 0 =
      (aritySection A 0 ▷ power X.carrier 0) ≫ X.action 0 := by
    simp only [homologyOperation, power, Iso.hom_inv_id_assoc]
  have hu : Homotopy ((oneIso X.carrier).inv ≫ homologyOperation X 1) (𝟙 X.carrier) := by
    simpa only [Iso.inv_hom_id] using
      (homologyUnaryHomotopy X).compLeft (oneIso X.carrier).inv
  have hc := (homologyCompositionHomotopy X 1 0 0).compLeft (oneIso X.carrier).inv
  rw [← hb] at hc
  rw [reassoc_of% (_root_.SerrePositivity.HomologyZero.nullaryBinaryInsertion X.carrier (homologyOperation X 0))] at hc
  simpa only [homologyBinary, Category.assoc] using (hu.symm.trans hc).symm

/-- 概要：E 代数の実際の H⁰ の積は左単位を持つ（BF §1、BM §1）。
方針：H⁰ の元を単位からの射で表し、左単位ホモトピーを前合成する。
規約：構成済みの nullary の類 homologyOne を使う。
使われ方：H⁰ の環の単位公理。 -/
lemma homologyProduct_one_left (X : (operad A).Algebra) (x : X.carrier.homology 0) :
    homologyProduct X (homologyOne X) x = x := by
  obtain ⟨f, rfl⟩ := _root_.SerrePositivity.HomologyZero.unitClass_surjective X.carrier x
  change _root_.SerrePositivity.HomologyZero.pairingValue (homologyBinary X)
    (_root_.SerrePositivity.HomologyZero.unitClass X.carrier (homologyOperation X 0))
    (_root_.SerrePositivity.HomologyZero.unitClass X.carrier f) = _
  rw [_root_.SerrePositivity.HomologyZero.pairingValue_class]
  apply (_root_.SerrePositivity.HomologyZero.unitClass_eq_iff X.carrier _ _).mpr
  have he : _root_.SerrePositivity.HomologyZero.unitPairing (homologyBinary X) (homologyOperation X 0) f =
      f ≫ (λ_ X.carrier).inv ≫ (homologyOperation X 0 ▷ X.carrier) ≫ homologyBinary X := by
    change (λ_ (𝟙_ (Complex A))).inv ≫ (homologyOperation X 0 ⊗ₘ f) ≫ homologyBinary X = _
    rw [tensorHom_def']
    simp only [Category.assoc]
    rw [reassoc_of% (leftUnitor_inv_naturality f).symm]
  refine ⟨(Homotopy.ofEq he).trans ?_⟩
  simpa only [Category.assoc, Category.comp_id] using
    (homologyBinaryLeftUnitHomotopy X).compLeft f

/-- 概要：E 代数の実際の H⁰ の積は右単位を持つ（BF §1、BM §1）。
方針：可換性と左単位則を合成する。
規約：元の homology 0 上の積。
使われ方：H⁰ の環の単位公理。 -/
lemma homologyProduct_one_right (X : (operad A).Algebra) (x : X.carrier.homology 0) :
    homologyProduct X x (homologyOne X) = x :=
  (homologyProduct_comm X x (homologyOne X)).trans (homologyProduct_one_left X x)

end SerrePositivity.EInfinity.BarrattEccles
