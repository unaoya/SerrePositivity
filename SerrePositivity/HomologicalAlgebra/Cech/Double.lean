module

public import SerrePositivity.HomologicalAlgebra.Cech.Basic
public import SerrePositivity.HomologicalAlgebra.Cech.Diagonal
public import Mathlib.CategoryTheory.Functor.Currying

/-!
概要：増大余単体図式の二方向の Čech 完全性を比較する。
方針：増大射と交代余面を二方向に取り、可換な微分を第一象限の二重複体に渡す。
規約：各方向で増大項を次数 0 に置く。
使われ方：環の二重 Čech 複体と、スキーム上の前層から作る二重図式。
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Preadditive
open scoped Simplicial

namespace SerrePositivity.Cech

set_option backward.isDefEq.respectTransparency false

/-- 増大 Čech 複体の次数に対応する増大単体。 -/
def simplex (n : ℕ) : AugmentedSimplexCategory :=
  match n with
  | 0 => .star
  | k + 1 => .of ⦋k⦌

/-- 増大と余面を共通に添字づける。 -/
def FaceIndex : ℕ → Type
  | 0 => Fin 1
  | n + 1 => Fin (n + 2)

instance (n : ℕ) : Fintype (FaceIndex n) := by cases n <;> exact inferInstanceAs (Fintype (Fin _))

/-- 増大と余面の射。 -/
def face : ∀ n, FaceIndex n → (simplex n ⟶ simplex (n + 1))
  | 0, _ => WithInitial.starInitial.to _
  | _ + 1, i => WithInitial.incl.map (SimplexCategory.δ i)

private def sign : ∀ n, FaceIndex n → ℤ
  | 0, _ => 1
  | n + 1, i => (-1) ^ (show Fin (n + 2) from i).val

/-- 二重図式の行の増大余単体対象。 -/
def row {C : Type*} [Category* C] (F : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤ C)
    (j : ℕ) : CosimplicialObject.Augmented C :=
  AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj
    ((Functor.curryObj F).flip.obj (simplex j))

/-- 二重図式の列の増大余単体対象。 -/
def col {C : Type*} [Category* C] (F : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤ C)
    (i : ℕ) : CosimplicialObject.Augmented C :=
  AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj
    ((Functor.curryObj F).obj (simplex i))

variable (F : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤ AddCommGrpCat)

private def obj (i j : ℕ) : AddCommGrpCat := F.obj (simplex i, simplex j)

private def dh (i j : ℕ) : obj F i j ⟶ obj F (i + 1) j :=
  ∑ k : FaceIndex i, sign i k • F.map (face i k, 𝟙 (simplex j))

private def dv (i j : ℕ) : obj F i j ⟶ obj F i (j + 1) :=
  ∑ k : FaceIndex j, sign j k • F.map (𝟙 (simplex i), face j k)

private theorem dh_comm (i j : ℕ) :
    dh F i j ≫ dv F (i + 1) j = dv F i j ≫ dh F i (j + 1) := by
  simp only [dh, dv, obj, sum_comp, comp_sum, zsmul_comp, comp_zsmul, Finset.smul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext l
  congr 1
  funext k
  rw [← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul, mul_comm, ← F.map_comp, ← F.map_comp]
  apply congrArg ((sign i l * sign j k) • ·)
  apply congrArg F.map
  apply Prod.ext
  · change face i l ≫ 𝟙 _ = 𝟙 _ ≫ face i l
    rw [Category.comp_id, Category.id_comp]
  · change 𝟙 _ ≫ face j k = face j k ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]

private theorem dh_at (i j : ℕ) : HEq (dh F i j) (differential (row F j) i) := by
  cases i with
  | zero =>
    apply heq_of_eq
    unfold dh
    change (∑ k : Fin 1, (1 : ℤ) • F.map (X := (simplex 0, simplex j)) (Y := (simplex 1, simplex j))
      (face 0 k, 𝟙 (simplex j))) = _
    rw [Fin.sum_univ_one, one_zsmul]
    rfl
  | succ i =>
    apply heq_of_eq
    rfl

private theorem dv_at (i j : ℕ) : HEq (dv F i j) (differential (col F i) j) := by
  cases j with
  | zero =>
    apply heq_of_eq
    unfold dv
    change (∑ k : Fin 1, (1 : ℤ) • F.map (X := (simplex i, simplex 0)) (Y := (simplex i, simplex 1))
      (𝟙 (simplex i), face 0 k)) = _
    rw [Fin.sum_univ_one, one_zsmul]
    rfl
  | succ j =>
    apply heq_of_eq
    rfl

private theorem dh_sq (i j : ℕ) : dh F i j ≫ dh F (i + 1) j = 0 := by
  cases i with
  | zero =>
    simp only [eq_of_heq (dh_at F 0 j), eq_of_heq (dh_at F 1 j)]
    exact differential_comp _ 0
  | succ i =>
    simp only [eq_of_heq (dh_at F (i + 1) j), eq_of_heq (dh_at F (i + 2) j)]
    exact differential_comp _ (i + 1)

private theorem dv_sq (i j : ℕ) : dv F i j ≫ dv F i (j + 1) = 0 := by
  cases j with
  | zero =>
    simp only [eq_of_heq (dv_at F i 0), eq_of_heq (dv_at F i 1)]
    exact differential_comp _ 0
  | succ j =>
    simp only [eq_of_heq (dv_at F i (j + 1)), eq_of_heq (dv_at F i (j + 2))]
    exact differential_comp _ (j + 1)

private theorem acyclic_iff (X : CosimplicialObject.Augmented AddCommGrpCat) :
    (augmentedCochain.obj X).Acyclic ↔
      (∀ x, differential X 0 x = 0 → x = 0) ∧
      ∀ n x, differential X (n + 1) x = 0 → ∃ y, differential X n y = x := by
  let K := augmentedCochain.obj X
  have h₀ : K.ExactAt 0 ↔ ∀ x, differential X 0 x = 0 → x = 0 := by
    rw [K.exactAt_iff' 0 0 1 (by simp) (by simp),
      ShortComplex.exact_iff_mono _ (K.shape 0 0 (by simp)),
      AddCommGrpCat.mono_iff_injective]
    change Function.Injective (K.d 0 1) ↔ _
    simp only [K, augmentedCochain_d]
    let d := (differential X 0).hom
    change Function.Injective d ↔ ∀ x, d x = 0 → x = 0
    exact ⟨fun h _ hx => h (hx.trans (map_zero d).symm),
      fun h x y hxy => sub_eq_zero.mp (h (x - y) (by rw [map_sub, hxy, sub_self]))⟩
  have hn (n : ℕ) : K.ExactAt (n + 1) ↔
      ∀ x, differential X (n + 1) x = 0 → ∃ y, differential X n y = x := by
    rw [K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp),
      ShortComplex.ab_exact_iff_function_exact]
    change Function.Exact (K.d n (n + 1)) (K.d (n + 1) (n + 2)) ↔ _
    simp only [K, augmentedCochain_d]
    exact ⟨fun h x => (h x).mp, fun h x => ⟨h x, fun ⟨y, hy⟩ => by
      rw [← hy]
      exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (differential_comp X n)) y⟩⟩
  exact ⟨fun h => ⟨h₀.mp (h 0), fun n => (hn n).mp (h (n + 1))⟩,
    fun ⟨h0, h⟩ n => match n with | 0 => h₀.mpr h0 | n + 1 => (hn n).mpr (h n)⟩

private theorem row_exact_iff (j : ℕ) :
    RowExact (fun i j => obj F i j) (fun i j => (dh F i j).hom) j ↔
      (augmentedCochain.obj (row F j)).Acyclic := by
  rw [acyclic_iff]
  dsimp only [RowExact]
  simp only [eq_of_heq (dh_at F 0 j)]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  cases i with
  | zero => simp only [eq_of_heq (dh_at F 0 j), eq_of_heq (dh_at F 1 j)]; rfl
  | succ i => simp only [eq_of_heq (dh_at F (i + 1) j), eq_of_heq (dh_at F (i + 2) j)]; rfl

private theorem col_exact_iff (i : ℕ) :
    ColExact (fun i j => obj F i j) (fun i j => (dv F i j).hom) i ↔
      (augmentedCochain.obj (col F i)).Acyclic := by
  rw [acyclic_iff]
  dsimp only [ColExact]
  simp only [eq_of_heq (dv_at F i 0)]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro j
  cases j with
  | zero => simp only [eq_of_heq (dv_at F i 0), eq_of_heq (dv_at F i 1)]; rfl
  | succ j => simp only [eq_of_heq (dv_at F i (j + 1)), eq_of_heq (dv_at F i (j + 2))]; rfl

/-- 二重増大余単体図式で、正次数の行と列が完全なら、二つの増大軸の完全性は同値。 -/
theorem doubleCech_acyclic_iff
    (hr : ∀ j, 0 < j → (augmentedCochain.obj (row F j)).Acyclic)
    (hc : ∀ i, 0 < i → (augmentedCochain.obj (col F i)).Acyclic) :
    (augmentedCochain.obj (row F 0)).Acyclic ↔ (augmentedCochain.obj (col F 0)).Acyclic := by
  rw [← row_exact_iff, ← col_exact_iff]
  apply exact_zero_row_iff_zero_col_of_commute
  · intro i j x
    exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (dh_sq F i j)) x
  · intro i j x
    exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (dv_sq F i j)) x
  · intro i j x
    exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (dh_comm F i j).symm) x
  · exact fun j hj => (row_exact_iff F j).mpr (hr j hj)
  · exact fun i hi => (col_exact_iff F i).mpr (hc i hi)

end SerrePositivity.Cech
