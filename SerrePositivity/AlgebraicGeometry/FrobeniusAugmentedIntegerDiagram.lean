module

public import SerrePositivity.AlgebraicGeometry.FrobeniusRingDiagram
public import SerrePositivity.AlgebraicGeometry.FrobeniusAugmentedRingCoefficients
public import SerrePositivity.AlgebraicGeometry.CechRingIntegerCoefficients

/-!
概要：元の増大環図式の項ごとのFrobenius係数を、同じ増大整数加群図式へ移す。
方針：既存の係数関手と増大単体との同値を使い、元のconerveでは恒等成分で照合する。
規約：元の増大項・余面・退化と既存のAugmentedRingCechExactの型を保つ。
使われ方：元の二重環Čechの各軸の実際のFrobenius係数の完全性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
variable {D E : AugmentedSimplexCategory ⥤ CommRingCat.{u}}
variable (p : ℕ) (hp : p.Prime)
variable (hD : ∀ j, (p : D.obj j) = 0) (hE : ∀ j, (p : E.obj j) = 0)

/-- 元の項ごとのFrobenius係数を、同じ増大整数加群図式へ見る。 -/
def frobeniusAugmentedIntegerDiagram (D : AugmentedSimplexCategory ⥤ CommRingCat.{u})
    (p : ℕ) (hp : p.Prime) (hD : ∀ j, (p : D.obj j) = 0) :
    CosimplicialObject.Augmented (ModuleCat.{u} ℤ) :=
  AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj
    (frobeniusRingDiagram D p hp hD)

/-- 元の増大図式の係数移送を、同じ既存の係数の自然変換で写す。 -/
def frobeniusAugmentedIntegerDiagramMap (η : D ⟶ E) :
    frobeniusAugmentedIntegerDiagram D p hp hD ⟶
      frobeniusAugmentedIntegerDiagram E p hp hE :=
  AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.map
    (frobeniusRingDiagramMap p hp hD (hE := hE) η)

/-- 元の増大図式の同型を、同じ既存の係数の同型で写す。 -/
def frobeniusAugmentedIntegerDiagramIso (e : D ≅ E) :
    frobeniusAugmentedIntegerDiagram D p hp hD ≅
      frobeniusAugmentedIntegerDiagram E p hp hE :=
  AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.mapIso
    (frobeniusRingDiagramIso p hp hD (hE := hE) e)

/-- 同じ実際のconerveでは、増大環係数の整数加群化と恒等成分で一致する。 -/
def frobeniusConerveIntegerDiagramIso (f : Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime)
    (hD : ∀ j, (p : (AugmentedSimplexCategory.equivAugmentedCosimplicialObject.inverse.obj
      f.augmentedCechConerve).obj j) = 0) :
    frobeniusAugmentedIntegerDiagram
      (AugmentedSimplexCategory.equivAugmentedCosimplicialObject.inverse.obj
        f.augmentedCechConerve) p hp hD ≅
      (CosimplicialObject.Augmented.whiskeringObj _ _ ringToCechIntegerModule).obj
        (frobeniusAugmentedRingCoefficients f p hp (hD .star)) := by
  refine Comma.isoMk (Iso.refl _) (NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_) ?_
  · intro n m a
    rfl
  · apply NatTrans.ext
    funext n
    rfl

/-- 元の忠実平坦な射のconerveの、同じ項ごとのFrobenius係数のČech完全性。 -/
theorem frobeniusConerveIntegerDiagram_acyclic_of_faithfullyFlat
    {A : CommRingCat.{u}} (B : Under A) [Module.FaithfullyFlat A B.right]
    (p : ℕ) (hp : p.Prime)
    (hD : ∀ j, (p : (AugmentedSimplexCategory.equivAugmentedCosimplicialObject.inverse.obj
      (Arrow.mk B.hom).augmentedCechConerve).obj j) = 0) :
    (SerrePositivity.Cech.augmentedCochain.obj (frobeniusAugmentedIntegerDiagram
      (AugmentedSimplexCategory.equivAugmentedCosimplicialObject.inverse.obj
        (Arrow.mk B.hom).augmentedCechConerve) p hp hD)).Acyclic := by
  have h := (ringCechExact_iff_integer_acyclic _).mp
    (frobeniusAugmentedRingCoefficients_exact_of_faithfullyFlat B p hp (hD .star))
  let e := SerrePositivity.Cech.augmentedCochain.mapIso
    (frobeniusConerveIntegerDiagramIso (Arrow.mk B.hom) p hp hD)
  intro n
  exact (h n).of_iso e.symm

end SerrePositivity.AlgebraicGeometry
