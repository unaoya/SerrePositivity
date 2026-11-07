module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
概要：増大余単体対象と環の Čech 完全性の共通 API。
方針：増大射と交代余面を一つの余鎖複体にまとめ、環の場合は加法群の完全性で測る。
規約：増大項を次数 0 とし、通常の余単体対象の次数 n は n + 1 に置く。
使われ方：可換環論での降下と、スキーム上の前層複体の比較。
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Preadditive
open scoped Simplicial

namespace SerrePositivity.Cech

section Additive

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- 増大項を次数 0 に置き、交代余面複体を次数 1 から並べる。 -/
def term (X : CosimplicialObject.Augmented C) : ℕ → C
  | 0 => X.left
  | n + 1 => X.right.obj ⦋n⦌

/-- 増大射に続く交代余面微分。 -/
def differential (X : CosimplicialObject.Augmented C) :
    ∀ n, term X n ⟶ term X (n + 1)
  | 0 => X.hom.app ⦋0⦌
  | n + 1 => AlternatingCofaceMapComplex.objD X.right n

@[simp]
theorem differential_comp (X : CosimplicialObject.Augmented C) (n : ℕ) :
    differential X n ≫ differential X (n + 1) = 0 := by
  cases n with
  | zero =>
    have h (i : Fin 2) : X.hom.app ⦋0⦌ ≫ X.right.δ i = X.hom.app ⦋1⦌ := by
      have hi := (X.hom.naturality (SimplexCategory.δ i)).symm
      change X.hom.app ⦋0⦌ ≫ X.right.δ i = 𝟙 _ ≫ X.hom.app ⦋1⦌ at hi
      simpa only [Category.id_comp] using hi
    change X.hom.app ⦋0⦌ ≫ (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • X.right.δ i) = 0
    rw [comp_sum]
    simp only [comp_zsmul, h, ← Finset.sum_smul, Fin.sum_neg_one_pow]
    norm_num
  | succ n => exact AlternatingCofaceMapComplex.d_squared X.right n

/-- 増大を含む余鎖複体を関手的に作る。 -/
def augmentedCochain : CosimplicialObject.Augmented C ⥤ CochainComplex C ℕ where
  obj X := CochainComplex.of (term X) (differential X) (differential_comp X)
  map {X Y} f := CochainComplex.ofHom
    (fun | 0 => f.left | n + 1 => f.right.app ⦋n⦌) (by
      intro n
      simp only [CochainComplex.of_d]
      cases n with
      | zero => exact CosimplicialObject.Augmented.w_app (n := ⦋0⦌) (η := f)
      | succ n =>
        have h := ((alternatingCofaceMapComplex C).map f.right).comm n (n + 1)
        simpa only [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
          AlternatingCofaceMapComplex.map, CochainComplex.of_d, differential, term] using h)
  map_id X := by
    ext n
    cases n <;> rfl
  map_comp f g := by
    ext n
    cases n <;> rfl

@[simp]
theorem augmentedCochain_d (X : CosimplicialObject.Augmented C) (n : ℕ) :
    (augmentedCochain.obj X).d n (n + 1) = differential X n :=
  CochainComplex.of_d _ _ _

end Additive

abbrev ringToAb : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

/-- 下書きと同じ増大の単射性と全次数の完全性。 -/
def AugmentedRingCechExact (X : CosimplicialObject.Augmented CommRingCat.{u}) : Prop :=
  let C := (alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (X.right ⋙ ringToAb)
  let ε := (X.hom.app ⦋0⦌).hom
  Function.Injective ε ∧ Function.Exact ε (fun x => (C.d 0 1) x) ∧
    ∀ n : ℕ, Function.Exact (fun x => (C.d n (n + 1)) x) (fun x => (C.d (n + 1) (n + 2)) x)

/-- 環の射の増大 Čech 複体が完全であること。 -/
abbrev IsCechExact (f : Arrow CommRingCat.{u}) : Prop :=
  AugmentedRingCechExact f.augmentedCechConerve

/-- 加法群に忘却した増大 Čech 複体を作る関手。 -/
def ringCochain : CosimplicialObject.Augmented CommRingCat.{u} ⥤
    CochainComplex AddCommGrpCat.{u} ℕ :=
  CosimplicialObject.Augmented.whiskeringObj _ _ ringToAb ⋙ augmentedCochain

set_option backward.isDefEq.respectTransparency false in
theorem ringCechExact_iff_acyclic (X : CosimplicialObject.Augmented CommRingCat.{u}) :
    AugmentedRingCechExact X ↔ (ringCochain.obj X).Acyclic := by
  let Y := (CosimplicialObject.Augmented.whiskeringObj _ _ ringToAb).obj X
  let K := augmentedCochain.obj Y
  have h₀ : K.ExactAt 0 ↔ Function.Injective (X.hom.app ⦋0⦌).hom := by
    rw [K.exactAt_iff' 0 0 1 (by simp) (by simp),
      ShortComplex.exact_iff_mono _ (K.shape 0 0 (by simp))]
    rw [AddCommGrpCat.mono_iff_injective]
    rfl
  have hs (n : ℕ) : K.ExactAt (n + 1) ↔
      Function.Exact (differential Y n) (differential Y (n + 1)) := by
    rw [K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp),
      ShortComplex.ab_exact_iff_function_exact]
    change Function.Exact (K.d n (n + 1)) (K.d (n + 1) (n + 2)) ↔ _
    simp only [K, augmentedCochain_d]
    rfl
  have hd (n : ℕ) :
      ((alternatingCofaceMapComplex AddCommGrpCat).obj (X.right ⋙ ringToAb)).d n (n + 1) =
      differential Y (n + 1) := by
    change (AlternatingCofaceMapComplex.obj (X.right ⋙ ringToAb)).d n (n + 1) =
      AlternatingCofaceMapComplex.objD (X.right ⋙ ringToAb) n
    exact CochainComplex.of_d (fun k : ℕ => (X.right ⋙ ringToAb).obj ⦋k⦌)
      (AlternatingCofaceMapComplex.objD _) n
  constructor
  · rintro ⟨h, h1, hn⟩ n
    cases n with
    | zero => exact h₀.mpr h
    | succ n =>
      cases n with
      | zero => exact (hs 0).mpr h1
      | succ n => exact (hs (n + 1)).mpr (by
          have h := hn n
          simp only [hd] at h
          exact h)
  · intro h
    exact ⟨h₀.mp (h 0), (hs 0).mp (h 1),
      fun n => by
        simp only [hd]
        exact (hs (n + 1)).mp (h (n + 2))⟩

section Additive

variable {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
  [Preadditive C] [Preadditive D]

private theorem map_objD (F : C ⥤ D) [F.Additive] (X : CosimplicialObject C)
    (n : ℕ) : F.map (AlternatingCofaceMapComplex.objD X n) =
      AlternatingCofaceMapComplex.objD (X ⋙ F) n := by
  simp only [AlternatingCofaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- 加法関手を増大余鎖複体に施す操作は、余単体対象に施してから複体を作る操作と可換。 -/
def mapAugmentedCochainIso (F : C ⥤ D) [F.Additive] (X : CosimplicialObject.Augmented C) :
    (F.mapHomologicalComplex (.up ℕ)).obj (augmentedCochain.obj X) ≅
      augmentedCochain.obj ((CosimplicialObject.Augmented.whiskeringObj _ _ F).obj X) :=
  HomologicalComplex.Hom.isoOfComponents (fun | 0 => Iso.refl _ | _ + 1 => Iso.refl _) (by
    intro i j hij
    obtain rfl : j = i + 1 := hij.symm
    cases i with
    | zero =>
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
        Functor.mapHomologicalComplex_obj_d, augmentedCochain_d]
      change 𝟙 _ ≫ F.map (X.hom.app ⦋0⦌) = F.map (X.hom.app ⦋0⦌)
      exact Category.id_comp _
    | succ i =>
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
        Functor.mapHomologicalComplex_obj_d, augmentedCochain_d]
      exact (map_objD F X.right i).symm)

end Additive

theorem acyclic_map_iff_of_exact {C : Type*} {D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℕ)
    (h : ∀ S : ShortComplex C, (S.map F).Exact ↔ S.Exact) :
    ((F.mapHomologicalComplex (.up ℕ)).obj K).Acyclic ↔ K.Acyclic := by
  apply forall_congr'
  intro n
  rw [HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff]
  exact h (K.sc n)

theorem ringCechExact_iff_of_iso {X Y : CosimplicialObject.Augmented CommRingCat}
    (e : X ≅ Y) : AugmentedRingCechExact X ↔ AugmentedRingCechExact Y := by
  simp only [ringCechExact_iff_acyclic]
  exact ⟨fun h n => (h n).of_iso (ringCochain.mapIso e),
    fun h n => (h n).of_iso (ringCochain.mapIso e.symm)⟩

end SerrePositivity.Cech
