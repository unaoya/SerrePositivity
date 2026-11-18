module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyCoefficientAction

/-!
# E 代数の選んだ一入力演算はホモトピーで恒等作用

概要：BF §1 の E(1) の可縮性から、選んだ零次一入力演算の恒等性を得る。
方針：収縮の切断をオペラッドの単位と比較し、代数の単位公理を使う。
規約：実際の一入力テンソル冪の単位因子を比較に含める。
使われ方：H⁰ の二項積の単位則。
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

/-- 概要：選んだ一入力の E 作用は恒等作用とホモトピック（BF §1）。
方針：二係数の augmentation が一であることから比較し、代数の単位則を使う。
規約：一入力冪から元の複体への射の比較。
使われ方：H⁰ の積の単位則の最後の簡約。 -/
def homologyUnaryHomotopy (X : (operad A).Algebra) :
    Homotopy (homologyOperation X 1) (oneIso X.carrier).hom := by
  have hc := coefficientHomotopy A 1 (aritySection A 1) (operad A).unit
    ((aritySection_augmentation A 1).trans (augmentation A).unit.symm)
  have ht := SerrePositivity.cochainTensorHomotopyLeft hc (𝟙 (power X.carrier 1))
  change Homotopy (aritySection A 1 ⊗ₘ 𝟙 (power X.carrier 1))
    ((operad A).unit ⊗ₘ 𝟙 (power X.carrier 1)) at ht
  simp only [tensorHom_id] at ht
  simpa only [homologyOperation, Category.assoc, X.unit_action, Iso.inv_hom_id_assoc] using
    (ht.compLeft (λ_ (power X.carrier 1)).inv).compRight (X.action 1)

/-- 概要：選んだ一入力演算は実際の H⁰ の類を変えない（BF §1）。
方針：一入力作用のホモトピーへ代表射を前合成し、単位因子を相殺する。
規約：元の homology 0 の類の等式。
使われ方：H⁰ の積の単位則。 -/
lemma homologyUnary_class (X : (operad A).Algebra) (f : 𝟙_ (Complex A) ⟶ X.carrier) :
    _root_.SerrePositivity.HomologyZero.unitClass X.carrier
      (f ≫ (oneIso X.carrier).inv ≫ homologyOperation X 1) =
      _root_.SerrePositivity.HomologyZero.unitClass X.carrier f := by
  apply (_root_.SerrePositivity.HomologyZero.unitClass_eq_iff X.carrier _ _).mpr
  refine ⟨?_⟩
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    (homologyUnaryHomotopy X).compLeft (f ≫ (oneIso X.carrier).inv)

end SerrePositivity.EInfinity.BarrattEccles
