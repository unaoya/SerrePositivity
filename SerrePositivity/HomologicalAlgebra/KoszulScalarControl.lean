module

public import SerrePositivity.HomologicalAlgebra.KoszulDirectedLimit
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Koszul 関手の線形性と係数加群の零化元

係数加群を零化する元は、任意の列・全次数の Koszul ホモロジーも同じ元で零化する。
Noether 性・有限性・列の正則性は不要。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory Limits
open HomologicalComplex.homotopyCofiber
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R]

/-- スカラー作用の錐を取る関手は R 線形。 -/
instance scalarConeFunctor_linear (a : R) : (scalarConeFunctor a).Linear R where
  map_smul {P Q} f r := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ext_from_X (smulId a P) (i + 1) i
      (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)
    · simp only [HomologicalComplex.smul_f_apply, Linear.comp_smul,
        scalarConeFunctor_inl_map, Linear.smul_comp]
    · simp only [HomologicalComplex.smul_f_apply, Linear.comp_smul,
        scalarConeFunctor_inr_map, Linear.smul_comp]

/-- 反復錐による Koszul 関手は R 線形。 -/
instance koszulFunctor_linear {e : ℕ} (z : Fin e → R) : (koszulFunctor z).Linear R := by
  induction e with
  | zero => change (𝟭 _).Linear R; infer_instance
  | succ e ih =>
    have := ih (Fin.init z)
    change (koszulFunctor (Fin.init z) ⋙ scalarConeFunctor (z (Fin.last e))).Linear R
    infer_instance

/-- 加群を係数とする Koszul 関手は加法的。 -/
instance koszulModuleFunctor_additive {e : ℕ} (z : Fin e → R) :
    (koszulModuleFunctor z).Additive := by
  unfold koszulModuleFunctor
  infer_instance

/-- 加群を係数とする Koszul 関手も R 線形。 -/
instance koszulModuleFunctor_linear {e : ℕ} (z : Fin e → R) :
    (koszulModuleFunctor z).Linear R := by
  unfold koszulModuleFunctor
  infer_instance

/-- 係数加群の零化元は、全次数の Koszul ホモロジーを同じ元で零化する。 -/
theorem koszulModuleHomology_annihilated {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} R) (r : R) (hr : ∀ m : M, r • m = 0) (q : ℤ) :
    ∀ x : ((koszulModuleFunctor z).obj M).homology q, r • x = 0 := by
  have hm : r • (𝟙 M) = 0 := by
    ext m
    exact hr m
  have hc := congrArg (fun f ↦ (koszulModuleFunctor z).map f) hm
  rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] at hc
  have hh := congrArg (fun f ↦ HomologicalComplex.homologyMap f q) hc
  rw [homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at hh
  intro x
  exact congrArg (fun f ↦ f.hom x) hh

/-- 係数加群の零化イデアルは全次数の Koszul ホモロジーの零化イデアルに含まれる。 -/
theorem annihilator_le_koszulModuleHomology {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} R) (q : ℤ) :
    Module.annihilator R M ≤ Module.annihilator R (((koszulModuleFunctor z).obj M).homology q) := by
  intro r hr
  rw [Module.mem_annihilator] at hr ⊢
  exact koszulModuleHomology_annihilated z M r hr q

/-- 係数制限後も、底環の元の像による零化を Koszul ホモロジーへ移せる。 -/
theorem koszulModuleHomology_annihilated_restrictScalars
    {S : Type u} [CommRing S] (φ : R →+* S) (M : ModuleCat.{u} S)
    {e : ℕ} (z : Fin e → R) (r : R) (hr : ∀ m : M, φ r • m = 0) (q : ℤ) :
    ∀ x : ((koszulModuleFunctor z).obj ((ModuleCat.restrictScalars φ).obj M)).homology q,
      r • x = 0 :=
  koszulModuleHomology_annihilated z ((ModuleCat.restrictScalars φ).obj M) r hr q

/-- 係数加群の短完全列は、Koszul 複体の短完全列を誘導する。 -/
theorem koszulModuleFunctor_shortExact {e : ℕ} (z : Fin e → R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    (S.map (koszulModuleFunctor z)).ShortExact := by
  unfold koszulModuleFunctor
  rw [ShortComplex.map_comp]
  exact koszulFunctor_shortExact z _
    (hS.map_of_exact (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0))

end SerrePositivity
