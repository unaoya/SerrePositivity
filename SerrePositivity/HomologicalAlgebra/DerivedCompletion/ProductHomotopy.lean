module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ProductHomology

/-! # 複体の直積へのホモトピーの組立

各成分で与えたホモトピーを一つのホモトピーへまとめる。
導来圏での直積の比較に必要な、実際の複体の射に関する一般補題。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)

/-- 各次数で、成分への射を複体の直積の項への射にまとめる。 -/
def complexProductDegreeLift (i : ℤ) {M : ModuleCat.{u} R}
    (g : ∀ n, M ⟶ (K n).X i) : M ⟶ (piObj K).X i :=
  ModuleCat.ofHom ((complexProductDegreeEquiv R K i).symm.toLinearMap.comp
    (LinearMap.pi (fun n ↦ (g n).hom)))

@[simp] theorem complexProductDegreeLift_projection (i : ℤ) {M : ModuleCat.{u} R}
    (g : ∀ n, M ⟶ (K n).X i) (n : ℕ) :
    complexProductDegreeLift R K i g ≫ (Pi.π K n).f i = g n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (Pi.π K n).f i ((complexProductDegreeEquiv R K i).symm (fun n ↦ g n x)) = g n x
  rw [← complexProductDegreeEquiv_apply]
  exact congrFun ((complexProductDegreeEquiv R K i).apply_symm_apply _) n

/-- 各次数の射は、全成分への射影によって決まる。 -/
theorem complexProductDegree_hom_ext (i : ℤ) {M : ModuleCat.{u} R}
    {f g : M ⟶ (piObj K).X i} (h : ∀ n, f ≫ (Pi.π K n).f i = g ≫ (Pi.π K n).f i) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (complexProductDegreeEquiv R K i).injective
  funext n
  simpa only [complexProductDegreeEquiv_apply, ModuleCat.hom_comp, LinearMap.comp_apply] using
    congrArg (fun f ↦ f.hom x) (h n)

/-- 各射影後のホモトピーを、直積への一つのホモトピーへまとめる。 -/
def complexProductHomotopy {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {f g : P ⟶ piObj K} (h : ∀ n, Homotopy (f ≫ Pi.π K n) (g ≫ Pi.π K n)) :
    Homotopy f g where
  hom i j := complexProductDegreeLift R K j (fun n ↦ (h n).hom i j)
  zero i j hij := by
    apply complexProductDegree_hom_ext R K j
    intro n
    rw [complexProductDegreeLift_projection, (h n).zero i j hij, zero_comp]
  comm i := by
    apply complexProductDegree_hom_ext R K i
    intro n
    rw [add_comp, add_comp, ← dNext_comp_right, ← prevD_comp_right]
    have hh : (fun i j ↦ complexProductDegreeLift R K j (fun n ↦ (h n).hom i j) ≫
        (Pi.π K n).f j) = (h n).hom := by
      funext i j
      exact complexProductDegreeLift_projection R K j _ n
    rw [hh]
    exact (h n).comm i

/-- 各射影後に零ホモトピックなら、直積への射も零ホモトピック。 -/
theorem complexProduct_nonempty_homotopy_zero {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ piObj K) (h : ∀ n, Nonempty (Homotopy (f ≫ Pi.π K n) 0)) :
    Nonempty (Homotopy f 0) := by
  refine ⟨complexProductHomotopy R K (fun n ↦ ?_)⟩
  simpa only [zero_comp] using (h n).some

end SerrePositivity.DerivedCompletion
