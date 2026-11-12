module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousRingChartMap
public import SerrePositivity.AlgebraicGeometry.GradedOriginalProjRingMapSections
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
概要：Proj の実際の引き戻しが、元の基底環の大域スカラーを保つことを示す。
方針：分母 1 の標準開で検査する。この開は全空間なので制限は単射。
規約：零次成分を大域切断全体と同一視する仮定は加えない。
使われ方：底変換と閉厚化の実際の構造層の Čech の射の係数の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory HomogeneousIdeal HomogeneousLocalization
universe u v w
variable {R S A : Type u} {ι : Type} [CommRing R] [CommRing S] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable {σ τ : Type u}
variable [SetLike σ S] [AddSubgroupClass σ S] [SMulMemClass σ R S]
variable [SetLike τ A] [AddSubgroupClass τ A] [SMulMemClass τ R A]
variable (G : ℕ → σ) (H : ℕ → τ) [GradedRing G] [GradedRing H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (f : G →+*ᵍ H) (g : S →ₐ[MvPolynomial ι R] A) (hfg : ∀ x, f x = g x)
variable (hf : (irrelevant H) ≤ (irrelevant G).map f)

include hfg in
/-- 基底環のスカラーの斉次分数は、実際の係数環の写像で保たれる。 -/
theorem gradedOriginalProjScalarNaturality_fraction (r : R) :
    Away.map f 1 (fromZeroRingHom G (Submonoid.powers (1 : S)) (gradedOriginalScalarToZero G r)) =
      fromZeroRingHom H (Submonoid.powers (f 1)) (gradedOriginalScalarToZero H r) := by
  change HomogeneousLocalization.map f _ (HomogeneousLocalization.mk _) = HomogeneousLocalization.mk _
  rw [HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective (Submonoid.powers (f 1))
  simp only [HomogeneousLocalization.val_mk]
  congr 1
  · change f (algebraMap R S r) = algebraMap R A r
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial ι R) S, hfg, g.commutes,
      ← IsScalarTower.algebraMap_apply R (MvPolynomial ι R) A]
  · apply Subtype.ext
    exact map_one f

include hfg in
/-- Proj の引き戻しは、元の基底環の大域スカラーを保つ。 -/
theorem gradedOriginalScalarToGlobalSections_naturality :
    gradedOriginalScalarToGlobalSections H =
      (Proj.map f hf).appTop.hom.comp (gradedOriginalScalarToGlobalSections G) := by
  ext r
  symm
  let F := Proj.map f hf
  let W := Proj.basicOpen H (f 1)
  have hW : W = ⊤ := by dsimp only [W]; rw [map_one, Proj.basicOpen_one]
  let res := (Proj H).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op
  haveI : IsIso (homOfLE (show W ≤ ⊤ from le_top)) := homOfLE_isIso_of_eq _ hW
  haveI : IsIso res := by dsimp only [res]; infer_instance
  apply (ConcreteCategory.bijective_of_isIso res).injective
  have hn := congrArg (fun k : Γ(Proj G, ⊤) ⟶ Γ(Proj H, W) ↦
      k.hom (gradedOriginalScalarToGlobalSections G r))
    (F.naturality (homOfLE (show Proj.basicOpen G 1 ≤ ⊤ from le_top)).op)
  have hl := gradedOriginalProjRingMapSections_apply G H f hf (SetLike.one_mem_graded G)
    (fromZeroRingHom G (Submonoid.powers (1 : S)) (gradedOriginalScalarToZero G r))
  change (F.appLE (Proj.basicOpen G 1) (F ⁻¹ᵁ Proj.basicOpen G 1) le_rfl).hom
    ((Proj.awayToSection G 1).hom
      (fromZeroRingHom G (Submonoid.powers (1 : S)) (gradedOriginalScalarToZero G r))) =
    (Proj.awayToSection H (f 1)).hom
      (Away.map f 1 (fromZeroRingHom G (Submonoid.powers (1 : S))
        (gradedOriginalScalarToZero G r))) at hl
  rw [Scheme.Hom.appLE_eq_app] at hl
  calc
    _ = (F.app (Proj.basicOpen G 1)).hom
        (((Proj G).presheaf.map (homOfLE (show Proj.basicOpen G 1 ≤ ⊤ from le_top)).op).hom
          (gradedOriginalScalarToGlobalSections G r)) := hn.symm
    _ = (F.app (Proj.basicOpen G 1)).hom ((Proj.awayToSection G 1).hom
        (fromZeroRingHom G (Submonoid.powers (1 : S)) (gradedOriginalScalarToZero G r))) := by
      rw [gradedOriginalScalarToGlobalSections_restrict G (SetLike.one_mem_graded G)]
    _ = (Proj.awayToSection H (f 1)).hom (fromZeroRingHom H (Submonoid.powers (f 1))
        (gradedOriginalScalarToZero H r)) := by
      rw [hl, gradedOriginalProjScalarNaturality_fraction G H f g hfg r]
    _ = _ := (gradedOriginalScalarToGlobalSections_restrict H (f.2 (SetLike.one_mem_graded G)) r).symm

end SerrePositivity.AlgebraicGeometry
