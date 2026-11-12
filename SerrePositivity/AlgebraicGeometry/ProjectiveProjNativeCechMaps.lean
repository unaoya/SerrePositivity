module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjCechComplexIso
public import SerrePositivity.AlgebraicGeometry.ProjectiveProjScalarNaturality
public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechRefinedPullback

/-!
概要：次数を保つ係数環の写像から、実際の Proj の標準開の Čech の射を作る。
方針：構造層の引き戻しと、逆像標準開から標準開への恒等添字の細分を合成する。
規約：大域スカラーの整合性を既に示した式から供給し、平坦性を仮定しない。
使われ方：閉厚化・基底変更・模型の遷移に対する標準開の計算の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory HomogeneousIdeal HomogeneousLocalization
universe u
variable {R S A : Type u} {ι : Type} [CommRing R] [CommRing S] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R S) (H : ℕ → Submodule R A) [GradedRing G] [GradedRing H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (f : G →+*ᵍ H) (g : S →ₐ[MvPolynomial ι R] A) (hfg : ∀ x, f x = g x)
variable (hf : (irrelevant H) ≤ (irrelevant G).map f)

include hfg in
/-- 実際の Proj の標準開の逆像は、次の係数環での同じ標準開。 -/
theorem projectiveProjNativeCech_preimageOpen (i : ι) :
    Proj.map f hf ⁻¹ᵁ projectiveProjCechOpen G i = projectiveProjCechOpen H i := by
  change Proj.map f hf ⁻¹ᵁ Proj.basicOpen G (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)) =
    Proj.basicOpen H (algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))
  rw [Proj.map_preimage_basicOpen, hfg, g.commutes]

/-- Proj の実際の構造層を引き戻す、標準開の Čech の射。 -/
def projectiveProjNativeCechMap :
    fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
      ModuleCat.restrictScalars (projectiveScalarToGlobalSections G))
        (projectiveProjCechOpen (ι := ι) G)) ⟶
    fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf (Proj H) ⋙
      ModuleCat.restrictScalars (projectiveScalarToGlobalSections H))
        (projectiveProjCechOpen (ι := ι) H)) :=
  schemeStructureCechRefinedPullbackMap (Proj.map f hf)
    (projectiveScalarToGlobalSections G) (projectiveScalarToGlobalSections H)
    (projectiveScalarToGlobalSections_naturality G H f g hfg hf)
    (projectiveProjCechOpen G) (projectiveProjCechOpen H) id
    (fun i ↦ le_of_eq (projectiveProjNativeCech_preimageOpen G H f g hfg hf i).symm)

end SerrePositivity.AlgebraicGeometry
