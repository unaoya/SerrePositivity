module

public import SerrePositivity.HomologicalAlgebra.Cech.Basic
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.SplitCechConerve
public import Mathlib.Algebra.Homology.QuasiIso

/-!
概要：環の射に左逆がある場合の増大 Čech 完全性。
方針：既存の SplitCechConerve の収縮を使い、正次数では定数余単体対象とホモロジーを比較する。
規約：環の射 A → B の左逆 B → A を取る。
使われ方：基底変換の後で切断が得られる場合と、二重 Čech 複体の行の完全性。
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Preadditive
open scoped Simplicial
open SerrePositivity.Cosimplicial

namespace SerrePositivity.Cech

set_option backward.isDefEq.respectTransparency false

private theorem const_d (A : AddCommGrpCat) (n : ℕ) :
    ((alternatingCofaceMapComplex AddCommGrpCat).obj
      ((Functor.const SimplexCategory).obj A)).d n (n + 1) =
      if Even n then 0 else 𝟙 A := by
  classical
  change (AlternatingCofaceMapComplex.obj ((Functor.const SimplexCategory).obj A)).d n
    (n + 1) = _
  unfold AlternatingCofaceMapComplex.obj
  simp only [CochainComplex.of_d]
  simp [AlternatingCofaceMapComplex.objD, CosimplicialObject.δ, ← Finset.sum_smul,
    Fin.sum_neg_one_pow, Nat.even_add_one]

/-- 左逆がある環の射の増大 Čech 複体は完全。 -/
theorem isCechExact_of_retraction (f : Arrow CommRingCat) (r : f.right ⟶ f.left)
    (hr : f.hom ≫ r = 𝟙 _) : IsCechExact f := by
  let E := f.augmentedCechConerve
  let L := alternatingCofaceMapComplex AddCommGrpCat
  let W := (Functor.whiskeringRight SimplexCategory CommRingCat AddCommGrpCat).obj ringToAb
  let ι := L.map (W.map E.hom)
  let π := L.map (W.map (cechRetraction f r hr))
  have hιπ : ι ≫ π = 𝟙 _ := by
    rw [← L.map_comp, ← W.map_comp, show E.hom ≫ cechRetraction f r hr = 𝟙 _ from
      cechAugmentation_retraction f r hr, W.map_id, L.map_id]
  have hπ : Homotopy (𝟙 _) (π ≫ ι) := by
    dsimp only [π, ι]
    rw [← L.map_comp, ← W.map_comp, ← L.map_id, ← W.map_id]
    exact ((cechSplitHomotopy f r hr).whiskerRight ringToAb).toCochainHomotopy
  let e : HomotopyEquiv _ _ :=
    ⟨ι, π, Homotopy.ofEq hιπ, hπ.symm⟩
  let := e.quasiIso_hom
  change AugmentedRingCechExact E
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (fun k => HomologicalComplex.Hom.f k 0) hιπ
    change ι.f 0 ≫ π.f 0 = 𝟙 _ at h
    have hl (a : f.left) : π.f 0 ((E.hom.app ⦋0⦌) a) = a :=
      DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom h) a
    exact Function.LeftInverse.injective hl
  · intro a
    constructor
    · intro ha
      have h := hπ.comm 0
      rw [prevD_eq_zero _ _ (by simp), dNext_eq _ (by simp : (ComplexShape.up ℕ).Rel 0 1)] at h
      have hx := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom h) a
      refine ⟨π.f 0 a, ?_⟩
      change (E.hom.app ⦋0⦌) (π.f 0 a) = a
      let K := L.obj (W.obj f.cechConerve)
      change a = hπ.hom 1 0 (K.d 0 1 a) +
        (0 : K.X 0) + (show K.X 0 from (ι.f 0) (π.f 0 a)) at hx
      have ha' : K.d 0 1 a = 0 := ha
      rw [ha', map_zero, zero_add, zero_add] at hx
      exact hx.symm
    · rintro ⟨b, rfl⟩
      let Y := (CosimplicialObject.Augmented.whiskeringObj _ _ ringToAb).obj E
      have h := differential_comp Y 0
      have hd : (L.obj (W.obj E.right)).d 0 1 =
          differential ((CosimplicialObject.Augmented.whiskeringObj _ _ ringToAb).obj E) 1 := by
        change (AlternatingCofaceMapComplex.obj (E.right ⋙ ringToAb)).d 0 1 =
          AlternatingCofaceMapComplex.objD (E.right ⋙ ringToAb) 0
        exact CochainComplex.of_d (fun n : ℕ => (E.right ⋙ ringToAb).obj ⦋n⦌) _ 0
      change (L.obj (W.obj E.right)).d 0 1 ((E.hom.app ⦋0⦌) b) = 0
      simp only [hd]
      exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom h) b
  · intro n
    have hconst : (L.obj (W.obj ((Functor.const _).obj f.left))).ExactAt (n + 1) := by
      rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
        ShortComplex.ab_exact_iff_function_exact]
      change Function.Exact
        (((alternatingCofaceMapComplex AddCommGrpCat).obj
          ((Functor.const SimplexCategory).obj (ringToAb.obj f.left))).d n (n + 1))
        (((alternatingCofaceMapComplex AddCommGrpCat).obj
          ((Functor.const SimplexCategory).obj (ringToAb.obj f.left))).d (n + 1) (n + 2))
      simp only [const_d]
      by_cases h : Even n
      · simp only [h, Nat.even_add_one, not_true_eq_false, ite_true, ite_false]
        change Function.Exact (fun _ : f.left => (0 : f.left)) (fun x => x)
        intro x
        simp
      · simp only [h, Nat.even_add_one, not_false_eq_true, ite_true, ite_false]
        change Function.Exact (fun x : f.left => x) (fun _ => (0 : f.left))
        intro x
        exact ⟨fun _ => ⟨x, rfl⟩, fun _ => rfl⟩
    have ht := (exactAt_iff_of_quasiIsoAt e.hom (n + 1)).mp hconst
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
      ShortComplex.ab_exact_iff_function_exact] at ht
    exact ht

end SerrePositivity.Cech
