module

public import SerrePositivity.PerfectComplex.Support
public import SerrePositivity.HomologicalAlgebra.FreeTerms
public import SerrePositivity.CommutativeAlgebra.KoszulExact
public import SerrePositivity.CommutativeAlgebra.KoszulBaseChange
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# 台つき完全複体の閉包性

`IsPerfectSupported z P`（有界・各項が有限自由・`z` に台をもつ）が、複体の同型・写像錐・シフト・
零複体・基底変更・ひねりで保たれることを示す。Koszul 複体 `K(x)` は `x` に台をもつ完全複体
（`koszulPerfSupp`）。

台の条件そのものの閉包性は `Support.lean`、各項の有限自由性の移送は
`HomologicalAlgebra/FreeTerms.lean`、基底変更・ひねりの `K₀` への作用は `K0Functor.lean`。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R] {e : ℕ} {z : Fin e → R}

/-! ## 同型・写像錐・シフト・零複体 -/

/-- 台つき完全複体は複体の同型で保たれる。 -/
lemma IsPerfectSupported.of_iso {P P' : CochainComplex (ModuleCat.{u} R) ℤ} (i : P ≅ P')
    (h : IsPerfectSupported z P) : IsPerfectSupported z P' where
  bounded := by
    obtain ⟨a, b, hab⟩ := h.bounded
    exact ⟨a, b, fun n hn ↦ (HomologicalComplex.Hom.isoApp i n).isZero_iff.mp (hab n hn)⟩
  free n := by
    have := h.free n
    exact Module.Free.of_equiv (HomologicalComplex.Hom.isoApp i n).toLinearEquiv
  finite n := by
    have := h.finite n
    exact Module.Finite.equiv (HomologicalComplex.Hom.isoApp i n).toLinearEquiv
  supported := by
    obtain ⟨v, hv⟩ := h.supported
    refine ⟨v, fun j ↦ ?_⟩
    obtain ⟨H⟩ := hv j
    refine ⟨(Homotopy.ofEq ?_).trans (((H.compRight i.hom).compLeft i.inv).trans
      (Homotopy.ofEq ?_))⟩
    · rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Iso.inv_hom_id]
    · simp

/-- 台つき完全複体の写像錐は台つき完全複体。 -/
lemma IsPerfectSupported.mappingCone {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (f : X ⟶ Y)
    (hX : IsPerfectSupported z X) (hY : IsPerfectSupported z Y) :
    IsPerfectSupported z (CochainComplex.mappingCone f) where
  bounded := by
    obtain ⟨a, b, hab⟩ := hX.bounded
    obtain ⟨c, d, hcd⟩ := hY.bounded
    refine ⟨min (a - 1) c, max b d, fun i hi ↦ ?_⟩
    rw [CochainComplex.mappingCone.isZero_X_iff]
    constructor
    · apply hab
      rcases hi with hi | hi
      · left; omega
      · right; omega
    · apply hcd
      rcases hi with hi | hi
      · left; omega
      · right; omega
  free i := by
    have := hX.free (i + 1); have := hY.free i
    have := hX.finite (i + 1); have := hY.finite i
    exact (mappingCone_free_finite f i).1
  finite i := by
    have := hX.free (i + 1); have := hY.free i
    have := hX.finite (i + 1); have := hY.finite i
    exact (mappingCone_free_finite f i).2
  supported := hX.supported.mappingCone f hY.supported

/-- 台つき完全複体のシフトは台つき完全複体。 -/
lemma IsPerfectSupported.shift {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : IsPerfectSupported z P) (n : ℤ) : IsPerfectSupported z (P⟦n⟧) where
  bounded := by
    obtain ⟨a, b, hab⟩ := hP.bounded
    exact ⟨a - n, b - n, fun i hi ↦ hab (i + n) (by omega)⟩
  free i := hP.free (i + n)
  finite i := hP.finite (i + n)
  supported := hP.supported.shift n

/-- 零複体は台つき完全複体。 -/
lemma isPerfectSupported_of_isZero {P : CochainComplex (ModuleCat.{u} R) ℤ} (hP : IsZero P) :
    IsPerfectSupported z P where
  bounded := ⟨0, 0, fun i _ ↦ (HomologicalComplex.eval _ _ i).map_isZero hP⟩
  free i := isZero_moduleCat_free ((HomologicalComplex.eval _ _ i).map_isZero hP)
  finite i := isZero_moduleCat_finite ((HomologicalComplex.eval _ _ i).map_isZero hP)
  supported := ⟨0, fun _ ↦ ⟨Homotopy.ofEq (hP.eq_of_src _ _)⟩⟩

/-! ## 基底変更 -/

section baseChange

variable {A C : Type u} [CommRing A] [CommRing C]

/-- 基底変更は各項の自由性を保つ。 -/
lemma free_baseChange (φ : A →+* C) (M : ModuleCat.{u} A) [Module.Free A M] :
    Module.Free C ((ModuleCat.extendScalars.{u, u, u} φ).obj M) := by
  let := φ.toAlgebra
  change Module.Free C (TensorProduct A C M)
  infer_instance

/-- 基底変更は各項の有限生成性を保つ。 -/
lemma finite_baseChange (φ : A →+* C) (M : ModuleCat.{u} A) [Module.Finite A M] :
    Module.Finite C ((ModuleCat.extendScalars.{u, u, u} φ).obj M) := by
  let := φ.toAlgebra
  change Module.Finite C (TensorProduct A C M)
  infer_instance

/-- 台つき完全複体は基底変更で保たれる。 -/
lemma isPerfectSupported_baseChange (φ : A →+* C) {e : ℕ} {z : Fin e → A}
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (h : IsPerfectSupported z P) :
    IsPerfectSupported (φ ∘ z) (baseChange φ P) where
  bounded := by
    obtain ⟨a, b, hab⟩ := h.bounded
    exact ⟨a, b, fun n hn ↦ (ModuleCat.extendScalars.{u, u, u} φ).map_isZero (hab n hn)⟩
  free n := by
    have := h.free n
    exact free_baseChange φ (P.X n)
  finite n := by
    have := h.finite n
    exact finite_baseChange φ (P.X n)
  supported := isSupported_baseChange φ h.supported

end baseChange

/-! ## ひねり -/

section twist

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T] {G : Type u} [Group G]
  [MulSemiringAction G T] [SMulCommClass G A T]

/-- `g⁻¹` の作用 `T ≃+* T`。 -/
noncomputable abbrev twistInvEquiv (g : G) : T ≃+* T := MulSemiringAction.toRingEquiv G T g⁻¹

instance (g : G) : RingHomInvPair (twistInvEquiv (T := T) g).toRingHom
    (twistInvEquiv (T := T) g).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (twistInvEquiv (T := T) g)

instance (g : G) : RingHomInvPair (twistInvEquiv (T := T) g).symm.toRingHom
    (twistInvEquiv (T := T) g).toRingHom :=
  RingHomInvPair.symm _ _

/-- ひねり `g^*M` は、`M` から恒等写像による `g⁻¹` 半線形同型を受ける。 -/
noncomputable def twistSemilinearEquiv (g : G) (M : ModuleCat.{u} T) :
    M ≃ₛₗ[(twistInvEquiv (T := T) g).toRingHom]
      (ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).obj M where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' t x := by
    change t • x = (g • (g⁻¹ • t)) • x
    rw [smul_inv_smul]
  left_inv _ := rfl
  right_inv _ := rfl

/-- 環自己同型に沿った係数制限は自由性を保つ。 -/
lemma free_twist (g : G) (M : ModuleCat.{u} T) [Module.Free T M] :
    Module.Free T ((ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).obj M) :=
  Module.Free.of_equiv (twistSemilinearEquiv g M)

/-- 環自己同型に沿った係数制限は有限生成性を保つ。 -/
lemma finite_twist (g : G) (M : ModuleCat.{u} T) [Module.Finite T M] :
    Module.Finite T ((ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).obj M) :=
  Module.Finite.of_surjective (twistSemilinearEquiv g M).toLinearMap
    (twistSemilinearEquiv g M).surjective

/-- `A` 上の作用によるひねりは、`A` から来る台をもつ完全複体を保つ。 -/
lemma isPerfectSupported_twist {e : ℕ} (z : Fin e → A) (g : G)
    {P : CochainComplex (ModuleCat.{u} T) ℤ} (h : IsPerfectSupported (algebraMap A T ∘ z) P) :
    IsPerfectSupported (algebraMap A T ∘ z) (twist g P) where
  bounded := by
    obtain ⟨a, b, hab⟩ := h.bounded
    exact ⟨a, b, fun n hn ↦
      (ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).map_isZero (hab n hn)⟩
  free n := by
    have := h.free n
    exact free_twist g (P.X n)
  finite n := by
    have := h.finite n
    exact finite_twist g (P.X n)
  supported := isSupported_twist z g h.supported

end twist

/-! ## Koszul 複体は台つき完全複体 -/

/-- Koszul 複体 `K(x)` は `x` に台をもつ完全複体。 -/
theorem isPerfectSupported_koszulComplex {n : ℕ} (x : Fin n → R) :
    IsPerfectSupported x (koszulComplex x) where
  bounded := ⟨-(n : ℤ), 0, fun i hi ↦ by
    rcases hi with hi | hi
    · exact koszulComplex_isZero_X_of_lt x i hi
    · exact koszulComplex_isZero_X_of_pos x i hi⟩
  free i := (koszulComplex_free_finite_X x i).1
  finite i := (koszulComplex_free_finite_X x i).2
  supported := isSupported_koszulComplex x

/-- `K₀^{(x)}` の元としての Koszul 複体。 -/
noncomputable def koszulPerfSupp {n : ℕ} (x : Fin n → R) : PerfSupp R x :=
  ⟨koszulComplex x, isPerfectSupported_koszulComplex x⟩

end SerrePositivity
