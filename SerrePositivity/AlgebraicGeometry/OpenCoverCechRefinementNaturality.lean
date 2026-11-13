module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCechRefinementIndependence

/-!
概要：細分の Čech 複体の写像を、係数の射と合成に自然なものにする。
方針：各タプルにおける制限の合成則を複体へ移す。
規約：通常の非増大 Čech 複体とその各次数の H を用いる。
使われ方：共通細分と底変換・閉厚化・Frobenius・余極限の比較の可換性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace
universe u v
variable {X : Type u} [TopologicalSpace X] {R : Type v} [CommRing R]
variable {ι κ ν : Type} [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
variable {P Q : (Opens X)ᵒᵖ ⥤ ModuleCat R}
variable (U : ι → Opens X) (V : κ → Opens X)
variable (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j))

/-- 細分の複体の射は係数前層の射に自然。 -/
theorem openCoverCechRefinementMap_naturality (η : P ⟶ Q) :
    openCoverCechRefinementMap P U V ρ hρ ≫ fullCechComplexMap (openCoverCechCoefficientMap η V) =
      fullCechComplexMap (openCoverCechCoefficientMap η U) ≫
        openCoverCechRefinementMap Q U V ρ hρ := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  exact openCoverCechRefinementCochains_naturality η U V ρ hρ (q + 1)

/-- 恒等細分が誘導する複体の射は恒等。 -/
theorem openCoverCechRefinementMap_id :
    openCoverCechRefinementMap P U U id (fun _ ↦ le_rfl) =
      𝟙 (fullCechComplex (openCoverCechDiagram P U)) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  exact openCoverCechRefinementCochains_id P U (q + 1)

/-- 細分の複体の射は細分の合成を保つ。 -/
theorem openCoverCechRefinementMap_comp (W : ν → Opens X)
    (σ : ν → κ) (hσ : ∀ l, W l ≤ V (σ l)) :
    openCoverCechRefinementMap P U V ρ hρ ≫ openCoverCechRefinementMap P V W σ hσ =
      openCoverCechRefinementMap P U W (ρ ∘ σ) (fun l ↦ (hσ l).trans (hρ (σ l))) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  exact openCoverCechRefinementCochains_comp P U V W ρ hρ σ hσ (q + 1)

/-- 各次数の Čech H の細分比較は、係数前層の射に自然。 -/
theorem openCoverCechRefinement_homology_naturality (η : P ⟶ Q) (q : ℕ) :
    HomologicalComplex.homologyMap (openCoverCechRefinementMap P U V ρ hρ) q ≫
        HomologicalComplex.homologyMap (fullCechComplexMap (openCoverCechCoefficientMap η V)) q =
      HomologicalComplex.homologyMap (fullCechComplexMap (openCoverCechCoefficientMap η U)) q ≫
        HomologicalComplex.homologyMap (openCoverCechRefinementMap Q U V ρ hρ) q := by
  simpa only [HomologicalComplex.homologyMap_comp] using congrArg
    (fun f ↦ HomologicalComplex.homologyMap f q)
    (openCoverCechRefinementMap_naturality U V ρ hρ η)

end SerrePositivity.AlgebraicGeometry
