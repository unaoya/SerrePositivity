module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.UniformZeroTowerHomology

/-! # The termwise torsion complex and its acyclic homotopy limit -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Termwise a-power torsion, with the original differential restricted to kernels. -/
abbrev powerTorsionComplex (n : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ where
  X i := ModuleCat.of R (powerTorsionModule a (K.X i) n)
  d i j := ModuleCat.ofHom
    { toFun := fun x ↦ ⟨K.d i j x, by
        change a ^ n • K.d i j (x : K.X i) = 0
        rw [← map_smul]
        exact congrArg (K.d i j) (show a ^ n • (x : K.X i) = 0 from x.property) |>.trans
          (map_zero _)⟩
      map_add' := fun x y ↦ Subtype.ext (map_add _ _ _)
      map_smul' := fun r x ↦ Subtype.ext (map_smul _ _ _) }
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f ↦ f.hom (x : K.X i)) (K.shape i j hij)
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f ↦ f.hom (x : K.X i)) (K.d_comp_d i j k)

/-- The actual torsion tower is connected by multiplication by a. -/
def powerTorsionComplexTransition (n : ℕ) :
    powerTorsionComplex a K (n + 1) ⟶ powerTorsionComplex a K n where
  f i := ModuleCat.ofHom (powerTorsionTransition a (K.X i) n)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact map_smul (K.d i j).hom a (x : K.X i)

/-- Complex composites retain the concrete a^k action in each degree. -/
theorem powerTorsionComplexComposite_coe (n k : ℕ) (i : ℤ)
    (x : (powerTorsionComplex a K (n + k)).X i) :
    (((complexTowerComposite R (powerTorsionComplex a K)
      (powerTorsionComplexTransition a K) n k).f i x :
      (powerTorsionComplex a K n).X i) : K.X i) = a ^ k • (x : K.X i) := by
  induction k with
  | zero => simp [complexTowerComposite]
  | succ k ih =>
    change (((complexTowerComposite R (powerTorsionComplex a K)
      (powerTorsionComplexTransition a K) n k).f i
      ((powerTorsionComplexTransition a K (n + k)).f i x) :
      (powerTorsionComplex a K n).X i) : K.X i) = _
    rw [ih]
    change a ^ k • (a • (x : K.X i)) = _
    rw [smul_smul, ← pow_succ]

/-- The coefficient ring's uniform torsion bound kills the torsion error holim
of every termwise flat complex, including unbounded complexes. -/
theorem powerTorsionComplex_holim_acyclic
    (hK : ∀ i, Module.Flat R (K.X i)) (N : ℕ)
    (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0) :
    (complexTowerHomotopyLimit R (powerTorsionComplex a K)
      (powerTorsionComplexTransition a K)).Acyclic := by
  apply complexTowerHolim_acyclic_of_uniform_zero R _ _ N
  intro n
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (((complexTowerComposite R (powerTorsionComplex a K)
    (powerTorsionComplexTransition a K) n N).f i x :
    (powerTorsionComplex a K n).X i) : K.X i) = 0
  rw [powerTorsionComplexComposite_coe]
  let := hK i
  exact flat_power_torsion_bound a N h (n + N) (x : K.X i) x.property

end SerrePositivity.DerivedCompletion
