module

public import SerrePositivity.PerfectComplex.K0
public import Mathlib.Algebra.Homology.HomotopyCofiber

/-!
# 基底変更とひねりの `K₀` への作用

- `K0.map φ`：基底変更 `K₀(A) → K₀(C)`（`φ : A →+* C`）。
- `K0.twistHom g`：ひねり `g^*` の誘導する準同型 `K₀(T) → K₀(T)`。`g • x := twistHom g⁻¹ x` で
  `G` の左作用（`K0.instDistribMulAction`、`K0.smul_mk`）。

台つき完全複体が基底変更・ひねりで保たれることは `Closure.lean`。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

namespace K0

section map

variable {A C : Type u} [CommRing A] [CommRing C] {e : ℕ} {z : Fin e → A}

/-- 基底変更の誘導する準同型 `K₀(A) → K₀(C)`。 -/
noncomputable def map (φ : A →+* C) : K0Supported A z →+ K0Supported C (φ ∘ z) :=
  lift (fun P ↦ mk ⟨baseChange φ P.1, isPerfectSupported_baseChange φ P.2⟩)
    (fun P P' h ↦ mk_eq_of_homotopyEquiv _ _
      ((ModuleCat.extendScalars.{u, u, u} φ).mapHomotopyEquiv h))
    (fun P P' f hc ↦ by
      have i : baseChange φ (CochainComplex.mappingCone f) ≅
          CochainComplex.mappingCone
            (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex _).map f) :=
        HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso f _
      have hc' := (isPerfectSupported_baseChange φ hc).of_iso i
      rw [mk_eq_of_homotopyEquiv ⟨_, isPerfectSupported_baseChange φ hc⟩ ⟨_, hc'⟩
        (HomotopyEquiv.ofIso i)]
      exact mk_cone ⟨baseChange φ P.1, isPerfectSupported_baseChange φ P.2⟩
        ⟨baseChange φ P'.1, isPerfectSupported_baseChange φ P'.2⟩ _ hc')

@[simp] lemma map_mk (φ : A →+* C) (P : PerfSupp A z) :
    map φ (mk P) = mk ⟨baseChange φ P.1, isPerfectSupported_baseChange φ P.2⟩ :=
  lift_mk _ _ _ _

end map

section twist

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T] {G : Type u} [Group G]
  [MulSemiringAction G T] [SMulCommClass G A T] {e : ℕ} {z : Fin e → A}

/-- ひねり `g^*` の誘導する準同型 `K₀(T) → K₀(T)`。 -/
noncomputable def twistHom (g : G) :
    K0Supported T (algebraMap A T ∘ z) →+ K0Supported T (algebraMap A T ∘ z) :=
  lift (fun P ↦ mk ⟨twist g P.1, isPerfectSupported_twist z g P.2⟩)
    (fun P P' h ↦ mk_eq_of_homotopyEquiv _ _
      ((ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).mapHomotopyEquiv h))
    (fun P P' f hc ↦ by
      have i : twist g (CochainComplex.mappingCone f) ≅
          CochainComplex.mappingCone
            (((ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).mapHomologicalComplex
              _).map f) :=
        HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso f _
      have hc' := (isPerfectSupported_twist z g hc).of_iso i
      rw [mk_eq_of_homotopyEquiv ⟨_, isPerfectSupported_twist z g hc⟩ ⟨_, hc'⟩
        (HomotopyEquiv.ofIso i)]
      exact mk_cone ⟨twist g P.1, isPerfectSupported_twist z g P.2⟩
        ⟨twist g P'.1, isPerfectSupported_twist z g P'.2⟩ _ hc')

@[simp] lemma twistHom_mk (g : G) (P : PerfSupp T (algebraMap A T ∘ z)) :
    twistHom (A := A) (z := z) g (mk P) = mk ⟨twist g P.1, isPerfectSupported_twist z g P.2⟩ :=
  lift_mk _ _ _ _

/-- `twist 1 P ≅ P`（各項の台集合は同じ）。 -/
noncomputable def twistOneIso (P : CochainComplex (ModuleCat.{u} T) ℤ) : twist (1 : G) P ≅ P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ ModuleCat.restrictScalarsId'App (MulSemiringAction.toRingHom G T 1)
      (by ext x; simp) (P.X i))
    (fun _ _ _ ↦ by ext; rfl)

/-- `twist a (twist b P) ≅ twist (b * a) P`（各項の台集合は同じ）。 -/
noncomputable def twistMulIso (a b : G) (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    twist a (twist b P) ≅ twist (b * a) P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (ModuleCat.restrictScalarsComp'App (MulSemiringAction.toRingHom G T a)
      (MulSemiringAction.toRingHom G T b) (MulSemiringAction.toRingHom G T (b * a))
      (by ext x; simp [mul_smul]) (P.X i)).symm)
    (fun _ _ _ ↦ by ext; rfl)

lemma twistHom_one : twistHom (A := A) (T := T) (z := z) (1 : G) = AddMonoidHom.id _ :=
  hom_ext fun P ↦ by
    rw [twistHom_mk, AddMonoidHom.id_apply]
    exact mk_eq_of_homotopyEquiv _ _ (HomotopyEquiv.ofIso (twistOneIso P.1))

lemma twistHom_mul (a b : G) :
    twistHom (A := A) (T := T) (z := z) (b * a) =
      (twistHom (A := A) (z := z) a).comp (twistHom (A := A) (z := z) b) :=
  hom_ext fun P ↦ by
    rw [AddMonoidHom.comp_apply, twistHom_mk, twistHom_mk, twistHom_mk]
    exact mk_eq_of_homotopyEquiv _ _ (HomotopyEquiv.ofIso (twistMulIso a b P.1)).symm

/-- `G` の `K₀(T)` への左作用：`g • x := (g⁻¹)^* x`。 -/
noncomputable instance instDistribMulAction :
    DistribMulAction G (K0Supported T (algebraMap A T ∘ z)) where
  smul g := twistHom (A := A) (z := z) g⁻¹
  one_smul x := by
    change twistHom (A := A) (z := z) (1 : G)⁻¹ x = x
    rw [inv_one, twistHom_one, AddMonoidHom.id_apply]
  mul_smul g h x := by
    change twistHom (A := A) (z := z) (g * h)⁻¹ x =
      twistHom (A := A) (z := z) g⁻¹ (twistHom (A := A) (z := z) h⁻¹ x)
    rw [mul_inv_rev, twistHom_mul, AddMonoidHom.comp_apply]
  smul_zero g := map_zero _
  smul_add g x y := map_add _ _ _

lemma smul_mk (g : G) (P : PerfSupp T (algebraMap A T ∘ z)) :
    g • mk P = mk ⟨twist g⁻¹ P.1, isPerfectSupported_twist z g⁻¹ P.2⟩ := by
  change twistHom (A := A) (z := z) g⁻¹ (mk P) = _
  exact twistHom_mk _ _

end twist

end K0

end SerrePositivity
