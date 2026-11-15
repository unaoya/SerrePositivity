module

public import SerrePositivity.AlgebraicGeometry.CoefficientPushoutDiagram
public import SerrePositivity.AlgebraicGeometry.FilteredRingArrowFactor
public import Mathlib.RingTheory.Noetherian.Basic

/-!
概要：旧模型の可換正方形を、実際の係数部分代数と pushout の同じ段へ因子化する。
方針：構成済みの両辺の余極限と係数の自然性に、一般の正方形の因子化を適用する。
規約：元の基底の Noether 性を要求せず、元の二射と正方形を保持する。
使われ方：B03・B04 の旧被覆模型から後の被覆係数模型への射の供給。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
open scoped TensorProduct
universe u

/-- 旧模型の正方形は、同じ実際の係数段へ係数・元の射・可換性を保って降りる。 -/
theorem exists_coefficientPushout_arrow_factor
    (A R S : Type u) [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] {C : Type u} [CommRing C] [Algebra R C]
    (e : R ⊗[A] S ≃ₐ[R] C)
    (k D E : Type u) [CommRing k] [IsNoetherianRing k]
    [CommRing D] [CommRing E] [Algebra k D] [Algebra k E]
    [Algebra.FiniteType k D] [Algebra.FiniteType k E]
    (κ : k →+* A) (t : D →ₐ[k] E) (a : D →+* R) (d : E →+* C)
    (ha : a.comp (algebraMap k D) = (algebraMap A R).comp κ)
    (hsq : d.comp t.toRingHom = (algebraMap R C).comp a) :
    ∃ (j : Finset R)
      (a₀ : D →+* (coefficientSubalgebraDiagram A R).obj j)
      (d₀ : E →+* (coefficientPushoutRingDiagram A R S).obj j),
      a₀.comp (algebraMap k D) = ((coefficientSubalgebraBaseNatTrans A R).app j).hom.comp κ ∧
      d₀.comp (algebraMap k E) = ((coefficientPushoutRootMap A R S).app j).hom.comp κ ∧
      ((coefficientSubalgebraCocone A R).ι.app j).hom.comp a₀ = a ∧
      ((coefficientPushoutRingCocone A R S e).ι.app j).hom.comp d₀ = d ∧
      ((coefficientPushoutBaseMap A R S).app j).hom.comp a₀ = d₀.comp t.toRingHom := by
  let α : (Functor.const (Finset R)).obj (CommRingCat.of k) ⟶
      coefficientSubalgebraDiagram A R :=
    (Functor.const (Finset R)).map (CommRingCat.ofHom κ) ≫
      coefficientSubalgebraBaseNatTrans A R
  have hD : (algebraMap k D).FinitePresentation :=
    RingHom.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hE : (algebraMap k E).FinitePresentation :=
    RingHom.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hα : ∀ j, CommRingCat.ofHom (algebraMap k D) ≫ CommRingCat.ofHom a =
      α.app j ≫ (coefficientSubalgebraCocone A R).ι.app j := by
    intro j
    change CommRingCat.ofHom (algebraMap k D) ≫ CommRingCat.ofHom a =
      (CommRingCat.ofHom κ ≫ (coefficientSubalgebraBaseNatTrans A R).app j) ≫ _
    rw [Category.assoc, coefficientSubalgebraCocone_base]
    exact CommRingCat.hom_ext ha
  obtain ⟨j, a₀, d₀, hκa, hκd, hea, hed, hcomm⟩ := exists_filtered_ring_arrow_factor
    (CommRingCat.of k) (coefficientSubalgebraDiagram A R) (coefficientPushoutRingDiagram A R S)
    (coefficientPushoutBaseMap A R S) α (coefficientSubalgebraCocone A R)
    (coefficientPushoutRingCocone A R S e) (coefficientSubalgebraCoconeIsColimit A R)
    (coefficientPushoutRingCoconeIsColimit A R S e) (CommRingCat.ofHom (algebraMap R C))
    (fun j ↦ (coefficientPushoutRingCocone_base A R S e j).symm)
    (CommRingCat.ofHom (algebraMap k D)) (CommRingCat.ofHom (algebraMap k E)) hD hE
    (CommRingCat.ofHom t.toRingHom) (CommRingCat.hom_ext t.comp_algebraMap)
    (CommRingCat.ofHom a) (CommRingCat.ofHom d) hα (CommRingCat.hom_ext hsq.symm)
  exact ⟨j, a₀.hom, d₀.hom, congrArg CommRingCat.Hom.hom hκa,
    congrArg CommRingCat.Hom.hom hκd, congrArg CommRingCat.Hom.hom hea,
    congrArg CommRingCat.Hom.hom hed, congrArg CommRingCat.Hom.hom hcomm⟩

end SerrePositivity.AlgebraicGeometry
