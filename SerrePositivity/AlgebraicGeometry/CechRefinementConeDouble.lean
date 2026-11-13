module

public import SerrePositivity.AlgebraicGeometry.CechRefinementConeMap
public import SerrePositivity.AlgebraicGeometry.CechRefinementConeHomology
public import SerrePositivity.HomologicalAlgebra.Cech.Diagonal

/-!
概要：二重 Čech 図式の行の cone を使って、零番の行の H の比較を得る。
方針：可換微分に対する B1 の行・列の完全性判定をそのまま使う。
規約：行は非負次数の複体。cone の零項は元の行の零項。
使われ方：共通アフィン細分の比較で、各交叉上の完全性を大域の比較へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R : Type u} [CommRing R]
variable (A B : ℕ → CochainComplex (ModuleCat.{u} R) ℕ)
variable (f : ∀ j, A j ⟶ B j)
variable (a : ∀ j, A j ⟶ A (j + 1)) (b : ∀ j, B j ⟶ B (j + 1))

/-- 行の cone を並べた二重図式の項。 -/
abbrev cechRefinementConeGrid (i j : ℕ) : Type u := cechRefinementConeTerm (A j) (B j) i

/-- 二重図式の水平方向は、各行の cone の微分。 -/
def cechRefinementConeHorizontal (i j : ℕ) :
    cechRefinementConeGrid A B i j →+ cechRefinementConeGrid A B (i + 1) j :=
  (cechRefinementConeDifferential (A j) (B j) (f j) i).toAddHom

/-- 二重図式の垂直方向は、二つの列方向の射の直積。 -/
def cechRefinementConeVertical (i j : ℕ) :
    cechRefinementConeGrid A B i j →+ cechRefinementConeGrid A B i (j + 1) :=
  (cechRefinementConeMapTerm (a j) (b j) i).toAddHom

/-- 列方向の二乗が零なら、cone の列方向の二乗も零。 -/
theorem cechRefinementConeVertical_squared
    (ha : ∀ j, a j ≫ a (j + 1) = 0) (hb : ∀ j, b j ≫ b (j + 1) = 0)
    (i j : ℕ) (x : cechRefinementConeGrid A B i j) :
    cechRefinementConeVertical A B a b i (j + 1)
      (cechRefinementConeVertical A B a b i j x) = 0 := by
  have h := LinearMap.congr_fun
    (cechRefinementConeMapTerm_comp (a j) (b j) (a (j + 1)) (b (j + 1)) i) x
  rw [ha, hb, cechRefinementConeMapTerm_zero] at h
  exact h

/-- 四角の可換性は、cone の二つの微分の可換性を与える。 -/
theorem cechRefinementConeGrid_commute
    (hf : ∀ j, f j ≫ b j = a j ≫ f (j + 1))
    (i j : ℕ) (x : cechRefinementConeGrid A B i j) :
    cechRefinementConeHorizontal A B f i (j + 1)
        (cechRefinementConeVertical A B a b i j x) =
      cechRefinementConeVertical A B a b (i + 1) j
        (cechRefinementConeHorizontal A B f i j x) :=
  (LinearMap.congr_fun (cechRefinementConeMapTerm_differential
    (a j) (b j) (hf j) i) x).symm

/-- 元の二重図式の列が完全なら、cone の各列も完全。 -/
theorem cechRefinementConeGrid_colExact
    (hA : ∀ i, SerrePositivity.Cech.ColExact (fun i j ↦ (A j).X i)
      (fun i j ↦ ((a j).f i).hom.toAddHom) i)
    (hB : ∀ i, SerrePositivity.Cech.ColExact (fun i j ↦ (B j).X i)
      (fun i j ↦ ((b j).f i).hom.toAddHom) i) (i : ℕ) :
    SerrePositivity.Cech.ColExact (cechRefinementConeGrid A B)
      (cechRefinementConeVertical A B a b) i := by
  cases i with
  | zero => exact hA 0
  | succ i =>
    constructor
    · intro x hx
      have hxB : ((b 0).f i).hom x.1 = 0 := congrArg Prod.fst hx
      have hxA : ((a 0).f (i + 1)).hom x.2 = 0 := congrArg Prod.snd hx
      exact Prod.ext ((hB i).1 x.1 hxB) ((hA (i + 1)).1 x.2 hxA)
    · intro j x hx
      have hxB : ((b (j + 1)).f i).hom x.1 = 0 := congrArg Prod.fst hx
      have hxA : ((a (j + 1)).f (i + 1)).hom x.2 = 0 := congrArg Prod.snd hx
      obtain ⟨yB, hyB⟩ := (hB i).2 j x.1 hxB
      obtain ⟨yA, hyA⟩ := (hA (i + 1)).2 j x.2 hxA
      exact ⟨(yB, yA), Prod.ext hyB hyA⟩

/-- 正の行の cone と全ての列が完全なら、零番の行の cone も完全。 -/
theorem cechRefinementConeGrid_zero_row_exact
    (ha : ∀ j, a j ≫ a (j + 1) = 0) (hb : ∀ j, b j ≫ b (j + 1) = 0)
    (hf : ∀ j, f j ≫ b j = a j ≫ f (j + 1))
    (hr : ∀ j, 0 < j → SerrePositivity.Cech.RowExact (cechRefinementConeGrid A B)
      (cechRefinementConeHorizontal A B f) j)
    (hA : ∀ i, SerrePositivity.Cech.ColExact (fun i j ↦ (A j).X i)
      (fun i j ↦ ((a j).f i).hom.toAddHom) i)
    (hB : ∀ i, SerrePositivity.Cech.ColExact (fun i j ↦ (B j).X i)
      (fun i j ↦ ((b j).f i).hom.toAddHom) i) :
    SerrePositivity.Cech.RowExact (cechRefinementConeGrid A B)
      (cechRefinementConeHorizontal A B f) 0 := by
  apply (SerrePositivity.Cech.exact_zero_row_iff_zero_col_of_commute
    (cechRefinementConeGrid A B) (cechRefinementConeHorizontal A B f)
    (cechRefinementConeVertical A B a b)
    (fun i j x ↦ LinearMap.congr_fun
      (cechRefinementConeDifferential_squared (A j) (B j) (f j) i) x)
    (cechRefinementConeVertical_squared A B a b ha hb)
    (cechRefinementConeGrid_commute A B f a b hf) hr
    (fun i _ ↦ cechRefinementConeGrid_colExact A B a b hA hB i)).mpr
  exact cechRefinementConeGrid_colExact A B a b hA hB 0

/-- B1 の二重図式の判定から得る、零番の行の Čech H の同型性。 -/
theorem cechRefinementConeGrid_homologyMap_isIso
    (ha : ∀ j, a j ≫ a (j + 1) = 0) (hb : ∀ j, b j ≫ b (j + 1) = 0)
    (hf : ∀ j, f j ≫ b j = a j ≫ f (j + 1))
    (hr : ∀ j, 0 < j → SerrePositivity.Cech.RowExact (cechRefinementConeGrid A B)
      (cechRefinementConeHorizontal A B f) j)
    (hA : ∀ i, SerrePositivity.Cech.ColExact (fun i j ↦ (A j).X i)
      (fun i j ↦ ((a j).f i).hom.toAddHom) i)
    (hB : ∀ i, SerrePositivity.Cech.ColExact (fun i j ↦ (B j).X i)
      (fun i j ↦ ((b j).f i).hom.toAddHom) i) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (f 0) q) := by
  have h := cechRefinementConeGrid_zero_row_exact A B f a b ha hb hf hr hA hB
  exact cechRefinementCone_homologyMap_isIso (A 0) (B 0) (f 0) h.1 h.2 q

end SerrePositivity.AlgebraicGeometry
