module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerUnit
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ConeBoundaryNormalization

/-! # ホモトピー逆極限の標準射影と両立する持ち上げ

標準三角形の連結射の符号と、具体的な複体の第1射影を照合する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable (R : Type u) [CommRing R]

/-- ホモトピー逆極限の候補から直積への、元を保つ標準射影。 -/
def complexTowerProjection
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n) :
    complexTowerHomotopyLimit R K t ⟶ piObj K :=
  CochainComplex.mappingCocone.fst (complexTowerDifference R K t)

/-- 差分を消す持ち上げは、標準射影によって元の写像へ戻る。 -/
theorem complexTowerHomotopyLimitLift_projection
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (g : P ⟶ piObj K)
    (hg : g ≫ complexTowerDifference R K t = 0) :
    complexTowerHomotopyLimitLift R K t P g hg ≫ complexTowerProjection R K t = g := by
  apply HomologicalComplex.hom_ext
  intro i
  have h := congrArg (fun γ ↦ γ.v i i (add_zero i))
    (complexTowerHomotopyLimitLift_fst R K t P g hg)
  simp only [CochainComplex.HomComplex.Cochain.comp_v
    (n₁ := -1) (n₂ := 1) (n₁₂ := 0) _ _ _ i (i + -1) i rfl (by omega)] at h
  change ((CochainComplex.HomComplex.Cochain.ofHom
    (complexTowerHomotopyLimitLift R K t P g hg)).rightUnshift (-1) (zero_add _)).v
      i (i + -1) rfl ≫
        (CochainComplex.mappingCone.fst (complexTowerDifference R K t)).1.v
          (i + -1) i (by omega) = g.f i at h
  rw [CochainComplex.HomComplex.Cochain.rightUnshift_v _ _ _ i (i + -1) rfl
    i (add_zero i)] at h
  simpa [complexTowerProjection, CochainComplex.mappingCocone.fst,
    CochainComplex.HomComplex.Cochain.leftShift,
    CochainComplex.shiftFunctorObjXIso] using h

/-- 両立する写像の持ち上げと標準射影の合成。 -/
theorem complexTowerCompatibleLift_comp_projection
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (g : ∀ n, P ⟶ K n)
    (hg : ∀ n, g (n + 1) ≫ t n = g n) :
    complexTowerCompatibleLift R K t P g hg ≫ complexTowerProjection R K t = Pi.lift g :=
  complexTowerHomotopyLimitLift_projection R K t P _ _

/-- Milnor列の連結射は、標準射影のホモロジー写像の負。 -/
theorem complexTowerHomologyBoundary_eq_neg_projection
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (i : ℤ) (x : (complexTowerHomotopyLimit R K t).homology i) :
    complexTowerHomologyBoundary R K t i x =
      -complexProductHomologyEquiv R K i
        (HomologicalComplex.homologyMap (complexTowerProjection R K t) i x) := by
  have h := congrArg (fun f ↦ f.hom x)
    (coneShiftBoundary_eq_neg_fst R (complexTowerDifference R K t) i)
  exact (congrArg (complexProductHomologyEquiv R K i) h).trans (map_neg _ _)

/-- Koszulの標準包含は、各段への実際の射影によって元の包含へ戻る。 -/
theorem koszulCompletionUnit_comp_projection {e : ℕ} (a : Fin e → R) (n : ℕ) :
    koszulCompletionUnit R a ≫
      complexTowerProjection R (powerKoszulTower R a) (powerKoszulTransition R a) ≫
        Pi.π (powerKoszulTower R a) n = koszulComplexInclusion R (fun i ↦ a i ^ n) := by
  rw [← assoc]
  rw [koszulCompletionUnit, complexTowerCompatibleLift_comp_projection, Pi.lift_comp_π]

end SerrePositivity.DerivedCompletion
