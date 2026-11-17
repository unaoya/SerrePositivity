module

public import SerrePositivity.AlgebraicGeometry.PairedPerfectCechBaseChangeColumns
public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalSection

/-!
概要：正次数で元の切断を持つ二変数Čechの列の完全性。
方針：同じ底変換の切断をD05に渡し、F05の同じ列へ代入する。
規約：切断の仮定を元の各正次数の射について保持する。
使われ方：アフィン細分の消去（承認済み計画F04）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
universe u

/-- 元の正次数の切断から、同じ列の増大totalの完全性を得る。 -/
theorem pairedCech_col_acyclic_of_sections {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A Y : Scheme.{u}} [IsAffine A]
    (h : A ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation h] [IsSeparated g] [QuasiCompact g]
    [LocallyOfFinitePresentation g]
    {κ : Type} [Fintype κ] [DecidableEq κ] (V : κ → Y.Opens)
    (hV : ∀ j, IsAffineOpen (V j)) (hcV : (⨆ j, V j) = ⊤)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (hσ : ∀ i : ℕ, 0 < i →
      ∃ s : (AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj (CategoryTheory.Arrow.mk h).augmentedCechNerve).obj (op (SerrePositivity.Cech.simplex i)) ⟶
        pullback g (augmentedNerveBase h (SerrePositivity.Cech.simplex i)),
        s ≫ pullback.snd g (augmentedNerveBase h (SerrePositivity.Cech.simplex i)) = 𝟙 _) :
    ∀ i : ℕ, 0 < i →
      (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ) (SerrePositivity.Cech.augmentedCochain.obj (SerrePositivity.Cech.col
        (pairedPerfectCech h g (fun _ : Unit ↦ ⊤) V p hp hR) i)) (.up ℕ)).Acyclic := by
  apply pairedCech_col_acyclic_of_baseChangeDescent h g V hV hcV p hp hR
  intro i hi
  obtain ⟨s, hs⟩ := hσ i hi
  exact perfectCechUniversalDescent_of_section p hp
    (pullback.snd g (augmentedNerveBase h (SerrePositivity.Cech.simplex i))) s hs

end SerrePositivity.AlgebraicGeometry
