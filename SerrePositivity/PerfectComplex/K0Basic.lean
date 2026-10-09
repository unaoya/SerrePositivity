module

public import SerrePositivity.PerfectComplex.Support
public import SerrePositivity.HomologicalAlgebra.FreeTerms
public import SerrePositivity.CommutativeAlgebra.KoszulExact
public import SerrePositivity.PerfectComplex.K0

/-!
# 台つき完全複体と `K₀` の基本事項（Lemma 3.5b の準備、段階 2）

- 台つき完全複体は写像錐・シフトで保たれる。
- `K₀` で、同型な複体は同じ類、零複体と可縮な複体の類は `0`、
  シフトは符号 `[P⟦n⟧] = (-1)^n [P]` を与える。
- Koszul 複体 `K(x)` は `x` に台をもつ完全複体。
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated ZeroObject

namespace SerrePositivity

variable {R : Type u} [CommRing R] {e : ℕ} {z : Fin e → R}

/-! ## 写像錐・シフトでの保存 -/

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

/-! ## `K₀` の基本事項 -/

namespace K0

/-- 同型な複体は同じ類。 -/
lemma mk_eq_of_iso (P P' : PerfSupp R z) (i : P.1 ≅ P'.1) : mk P = mk P' :=
  mk_eq_of_homotopyEquiv P P' (HomotopyEquiv.ofIso i)

/-- 零複体の類は `0`。 -/
lemma mk_eq_zero_of_isZero (P : PerfSupp R z) (hP : IsZero P.1) : mk P = 0 := by
  have hc : IsZero (CochainComplex.mappingCone (𝟙 P.1)) := by
    refine isZero_of_isZero_X fun i ↦ ?_
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨(HomologicalComplex.eval _ _ _).map_isZero hP,
      (HomologicalComplex.eval _ _ _).map_isZero hP⟩
  have h1 := mk_cone P P (𝟙 P.1) (isPerfectSupported_of_isZero hc)
  have h2 := mk_eq_of_iso ⟨_, isPerfectSupported_of_isZero hc⟩ P (hc.iso hP)
  rw [sub_self] at h1
  rw [← h2, h1]

/-- 恒等射が零ホモトピックな（可縮な）複体の類は `0`。 -/
lemma mk_eq_zero_of_homotopy_id_zero (P : PerfSupp R z) (h : Homotopy (𝟙 P.1) 0) : mk P = 0 := by
  have hZ : IsZero (0 : CochainComplex (ModuleCat.{u} R) ℤ) := isZero_zero _
  let E : HomotopyEquiv P.1 0 :=
    { hom := 0
      inv := 0
      homotopyHomInvId := (Homotopy.ofEq (by simp)).trans h.symm
      homotopyInvHomId := Homotopy.ofEq (hZ.eq_of_src _ _) }
  rw [mk_eq_of_homotopyEquiv P ⟨0, isPerfectSupported_of_isZero hZ⟩ E,
    mk_eq_zero_of_isZero _ hZ]

/-- `Cone(P → 0) ≅ P⟦1⟧`（ホモトピー圏で）。 -/
noncomputable def mappingConeToZeroIso (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (homotopyQuot R).obj (CochainComplex.mappingCone (0 : P ⟶ 0)) ≅
      (homotopyQuot R).obj (P⟦(1 : ℤ)⟧) := by
  have hZ : IsZero ((homotopyQuot R).obj (0 : CochainComplex (ModuleCat.{u} R) ℤ)) :=
    Functor.map_isZero _ (isZero_zero _)
  let T₂ := Triangle.mk (0 : (homotopyQuot R).obj P ⟶ 0) 0 (𝟙 (((homotopyQuot R).obj P)⟦(1 : ℤ)⟧))
  let e := isoTriangleOfIso₁₂ (CochainComplex.mappingCone.triangleh (0 : P ⟶ 0)) T₂
    (HomotopyCategory.mappingCone_triangleh_distinguished _) (contractible_distinguished₂ _)
    (Iso.refl _) (hZ.iso (isZero_zero _)) ((isZero_zero _).eq_of_tgt _ _)
  exact Triangle.π₃.mapIso e ≪≫ (((homotopyQuot R).commShiftIso (1 : ℤ)).app P).symm

/-- シフト 1 は符号を変える：`[P⟦1⟧] = -[P]`。 -/
lemma mk_shift_one (P : PerfSupp R z) : mk ⟨P.1⟦(1 : ℤ)⟧, P.2.shift 1⟩ = -mk P := by
  have hZ : IsZero (0 : CochainComplex (ModuleCat.{u} R) ℤ) := isZero_zero _
  let Z : PerfSupp R z := ⟨0, isPerfectSupported_of_isZero hZ⟩
  have hc := P.2.mappingCone (0 : P.1 ⟶ 0) Z.2
  have h1 := mk_cone P Z (0 : P.1 ⟶ 0) hc
  rw [mk_eq_zero_of_isZero Z hZ, zero_sub] at h1
  rw [← h1]
  exact (mk_eq_of_homotopyEquiv _ _
    (HomotopyCategory.homotopyEquivOfIso (mappingConeToZeroIso P.1))).symm

/-- シフトは符号 `(-1)^n` を与える。 -/
lemma mk_shift (P : PerfSupp R z) (n : ℤ) :
    mk ⟨P.1⟦n⟧, P.2.shift n⟩ = ((n.negOnePow : ℤˣ) : ℤ) • mk P := by
  induction n using Int.induction_on with
  | zero =>
    rw [Int.negOnePow_zero, Units.val_one, one_smul]
    exact mk_eq_of_iso _ _ ((shiftFunctorZero _ ℤ).app P.1)
  | succ n ih =>
    have h := mk_eq_of_iso ⟨P.1⟦(n + 1 : ℤ)⟧, P.2.shift _⟩
      ⟨(P.1⟦(n : ℤ)⟧)⟦(1 : ℤ)⟧, (P.2.shift _).shift 1⟩
      ((shiftFunctorAdd' _ (n : ℤ) 1 (n + 1) rfl).app P.1)
    rw [h, mk_shift_one ⟨P.1⟦(n : ℤ)⟧, P.2.shift _⟩, ih, Int.negOnePow_succ, Units.val_neg,
      neg_smul]
  | pred n ih =>
    have h := mk_eq_of_iso ⟨P.1⟦(-n : ℤ)⟧, P.2.shift _⟩
      ⟨(P.1⟦(-n - 1 : ℤ)⟧)⟦(1 : ℤ)⟧, (P.2.shift _).shift 1⟩
      ((shiftFunctorAdd' _ (-n - 1 : ℤ) 1 (-n) (by omega)).app P.1)
    rw [mk_shift_one ⟨P.1⟦(-n - 1 : ℤ)⟧, P.2.shift _⟩, ih] at h
    rw [← neg_neg (mk ⟨P.1⟦(-n - 1 : ℤ)⟧, _⟩), ← h, Int.negOnePow_sub, Int.negOnePow_one,
      mul_neg, mul_one, Units.val_neg, neg_smul]

end K0

/-! ## Koszul 複体は台つき完全複体 -/

/-- Koszul 複体は `-n` 次より下で零。 -/
lemma koszulComplex_isZero_X_of_lt :
    ∀ {n : ℕ} (x : Fin n → R) (i : ℤ), i < -(n : ℤ) → IsZero ((koszulComplex x).X i)
  | 0, x, i, hi => by
    rw [koszulComplex_zero]
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  | n + 1, x, i, hi => by
    rw [koszulComplex_succ, CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨koszulComplex_isZero_X_of_lt (Fin.init x) (i + 1) (by omega),
      koszulComplex_isZero_X_of_lt (Fin.init x) i (by omega)⟩

/-- Koszul 複体の項は有限自由。 -/
lemma koszulComplex_free_finite_X :
    ∀ {n : ℕ} (x : Fin n → R) (i : ℤ),
      Module.Free R ((koszulComplex x).X i) ∧ Module.Finite R ((koszulComplex x).X i)
  | 0, x, i => by
    rw [koszulComplex_zero]
    by_cases hi : i = 0
    · subst hi
      let e := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).toLinearEquiv
      exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩
    · have h := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
        (ModuleCat.of R R) i hi
      exact ⟨isZero_moduleCat_free h, isZero_moduleCat_finite h⟩
  | n + 1, x, i => by
    rw [koszulComplex_succ]
    obtain ⟨h1, h2⟩ := koszulComplex_free_finite_X (Fin.init x) (i + 1)
    obtain ⟨h3, h4⟩ := koszulComplex_free_finite_X (Fin.init x) i
    exact mappingCone_free_finite _ i

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
