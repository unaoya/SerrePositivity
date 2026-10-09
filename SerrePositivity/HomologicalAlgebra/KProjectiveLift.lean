module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# K 射影性による持ち上げ（Lemma 3.5b の準備、段階 3 の前半）

- `toSingleOfHomology`：`1` 次への微分が `0` の複体 `L` と `ε : H^0(L) → M` から作る
  鎖写像 `L → M[0]`。`H^0` で `ε` を誘導する。
- `exists_lift_of_quasiIso`：K 射影的な複体 `Q` からの鎖写像は、擬同型 `s : X → Y` に沿って
  ホモトピーを除いて持ち上がる。Mathlib の `CochainComplex.IsKProjective.Qh_map_bijective` による。
- Koszul 複体の添加写像 `K(z) → (A/(z))[0]` は（`K(z)` が分解なら）擬同型。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

/-! ## `H^0` から単一複体への写像 -/

section toSingle

variable {R : Type u} [CommRing R] (L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.d 0 1 = 0)
  {M : ModuleCat.{u} R}

/-- `1` 次への微分が `0` の複体 `L` と `ε : H^0(L) → M` から作る鎖写像 `L → M[0]`。 -/
noncomputable def toSingleOfHomology (ε : L.homology 0 ⟶ M) :
    L ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M :=
  HomologicalComplex.mkHomToSingle (L.pOpcycles 0 ≫ (L.isoHomologyι 0 1 (by simp) hL).inv ≫ ε)
    (fun i _ ↦ by rw [HomologicalComplex.d_pOpcycles_assoc, zero_comp])

/-- `toSingleOfHomology L hL ε` は `H^0` で `ε` を誘導する。 -/
lemma toSingleOfHomology_homologyMap (ε : L.homology 0 ⟶ M) :
    HomologicalComplex.homologyMap (toSingleOfHomology L hL ε) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso _ 0 M).hom = ε := by
  rw [← cancel_epi (L.homologyπ 0), HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom, HomologicalComplex.cyclesMap_i_assoc,
    toSingleOfHomology, HomologicalComplex.mkHomToSingle_f, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ← Category.assoc (L.iCycles 0),
    ← HomologicalComplex.homology_π_ι, Category.assoc,
    HomologicalComplex.isoHomologyι_hom_inv_id_assoc]

/-- `ε` が同型なら `toSingleOfHomology L hL ε` は `0` 次で擬同型。 -/
lemma quasiIsoAt_toSingleOfHomology (ε : L.homology 0 ⟶ M) [IsIso ε] :
    QuasiIsoAt (toSingleOfHomology L hL ε) 0 := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h := toSingleOfHomology_homologyMap L hL ε
  have : HomologicalComplex.homologyMap (toSingleOfHomology L hL ε) 0 =
      ε ≫ (HomologicalComplex.singleObjHomologySelfIso _ 0 M).inv := by
    rw [← cancel_mono (HomologicalComplex.singleObjHomologySelfIso _ 0 M).hom, h,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [this]
  infer_instance

/-- `0` 以外でホモロジーが消えていれば、`ε` が同型のとき `toSingleOfHomology` は擬同型。 -/
lemma quasiIso_toSingleOfHomology (ε : L.homology 0 ⟶ M) [IsIso ε]
    (h : ∀ i : ℤ, i ≠ 0 → IsZero (L.homology i)) : QuasiIso (toSingleOfHomology L hL ε) := by
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = 0
  · subst hi
    exact quasiIsoAt_toSingleOfHomology L hL ε
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    exact ⟨0, (h i hi).eq_of_src _ _,
      (HomologicalComplex.isZero_single_obj_homology _ _ M i hi).eq_of_src _ _⟩

end toSingle

/-! ## K 射影的な複体からの持ち上げ -/

section lift

variable {C : Type*} [Category C] [Abelian C]

/-- K 射影的な複体 `Q` からの鎖写像 `g : Q → Y` は、擬同型 `s : X → Y` に沿って
ホモトピーを除いて持ち上がる。 -/
lemma exists_lift_of_quasiIso {Q X Y : CochainComplex C ℤ} [Q.IsKProjective] (s : X ⟶ Y)
    [QuasiIso s] (g : Q ⟶ Y) : ∃ f : Q ⟶ X, Nonempty (Homotopy (f ≫ s) g) := by
  let := HasDerivedCategory.standard C
  obtain ⟨f', hf'⟩ := (CochainComplex.IsKProjective.Qh_map_bijective Q _).surjective
    ((DerivedCategory.quotientCompQhIso C).hom.app Q ≫ DerivedCategory.Q.map g ≫
      inv (DerivedCategory.Q.map s) ≫ (DerivedCategory.quotientCompQhIso C).inv.app X)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f'
  refine ⟨f, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (CochainComplex.IsKProjective.Qh_map_bijective Q _).injective
  rw [Functor.map_comp, Functor.map_comp, hf']
  simp only [Category.assoc, ← DerivedCategory.quotientCompQhIso_inv_naturality,
    IsIso.inv_hom_id_assoc]
  rw [← Category.assoc, ← DerivedCategory.quotientCompQhIso_hom_naturality, Category.assoc,
    Iso.hom_inv_id_app]
  exact Category.comp_id _

end lift

end SerrePositivity
