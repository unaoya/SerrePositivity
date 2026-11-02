module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# K 射影性による持ち上げ

## 概要

Lemma 3.5b の証明（`PerfectComplex/KoszulGeneration.lean`）では、台つき完全複体 `Q` の類 `[Q] ∈ K₀`
を Koszul 複体の類 `[K(z)]` の整数倍で表すために、全射 `H^0(Q) → k = A/(z)` を鎖写像 `Q → K(z)` に
持ち上げる。このファイルはそのための二つの道具を用意する。

- `toSingleOfHomology`：`1` 次への微分が零の複体 `L` と射 `ε : H^0(L) → M` から、鎖写像
  `L → M[0]`（`M` を `0` 次に置いた複体への射）を作る。`0` 次の成分は `L^0 → H^0(L) → M`。
  `ε` が同型で `L` のホモロジーが `0` 次に集中していれば、これは擬同型である
  （`quasiIso_toSingleOfHomology`）。
- `exists_lift_of_quasiIso`：K 射影的な複体 `Q` からの鎖写像 `g : Q → Y` は、擬同型 `s : X → Y` に
  沿ってホモトピーを除いて持ち上がる（`f : Q → X` で `f ≫ s ∼ g`）。導来圏では擬同型が可逆で、
  K 射影的な対象からの射についてはホモトピー圏の射と導来圏の射が一致する（Mathlib の
  `IsKProjective.Qh_map_bijective`）ことによる。

## 使われ方

`Q`（有界で項が射影的なので K 射影的）から `k[0]` への射を、擬同型 `K(z) → k[0]`
（Koszul 複体の添加写像、`CommutativeAlgebra/Koszul/Resolution.lean`）に沿って持ち上げる。
`CommutativeAlgebra/Truncate.lean` では、K 射影的な複体の間の擬同型がホモトピー同値であることを
Mathlib から直接使う。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

/-! ## `H^0` から単一複体への写像 -/

section toSingle

variable {R : Type u} [CommRing R] (L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.d 0 1 = 0)
  {M : ModuleCat.{u} R}

/-- `1` 次への微分 `L^0 → L^1` が零の複体 `L` と、射 `ε : H^0(L) → M` から作る鎖写像 `L → M[0]`。
`0` 次の成分は `L^0 → (0 次の余サイクル) → H^0(L) → M`（出ていく微分が零なので `0` 次ホモロジーは
余サイクル `L^0 / im d^{-1}` に等しい）、他の次数は零。`d^{-1}` と合成すると零になるので鎖写像の
条件をみたす（Mathlib の `mkHomToSingle`）。 -/
noncomputable def toSingleOfHomology (ε : L.homology 0 ⟶ M) :
    L ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M :=
  HomologicalComplex.mkHomToSingle (L.pOpcycles 0 ≫ (L.isoHomologyι 0 1 (by simp) hL).inv ≫ ε)
    (fun i _ ↦ by rw [HomologicalComplex.d_pOpcycles_assoc, zero_comp])

/-- `toSingleOfHomology L hL ε` が `0` 次ホモロジーに誘導する射は、`M[0]` の `0` 次ホモロジーを `M` と
同一視すれば `ε` である。ホモロジーへの射影 `homologyπ` で左から消し、構成に使った同型を順に
ほどいて確かめる。 -/
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

/-- `ε` が同型なら、`toSingleOfHomology L hL ε` は `0` 次で擬同型（`0` 次ホモロジーの射が同型）である。
`toSingleOfHomology_homologyMap` から、その射は `ε` と同型の合成だから。 -/
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

/-- `ε` が同型で、`L` のホモロジーが `0` 次以外で零なら、`toSingleOfHomology L hL ε` は擬同型である。
`0` 次は `quasiIsoAt_toSingleOfHomology`、他の次数は両辺のホモロジーが零なので自動的に同型。
Koszul 複体の添加写像 `K(z) → (A/(z))[0]` が擬同型であること（`quasiIso_koszulAugmentation`）に使う。 -/
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

/-- K 射影的な複体 `Q` からの鎖写像 `g : Q ⟶ Y` は、擬同型 `s : X ⟶ Y` に沿ってホモトピーを除いて
持ち上がる：`f : Q ⟶ X` で、`f ≫ s` が `g` とホモトピックなものがある。

証明は導来圏 `D(C)` で行う。`s` は導来圏で可逆なので `g ∘ s⁻¹` が導来圏の射 `Q → X` として定まる。
K 射影的な `Q` からの射については、ホモトピー圏から導来圏への写像が全単射（Mathlib の
`IsKProjective.Qh_map_bijective`）なので、この射はホモトピー圏の射 `f` から来る。同じ全単射の
単射性から `f ≫ s = g` がホモトピー圏で成り立ち、それは `f ≫ s` と `g` の間のホモトピーの存在と
同じである（`homotopyOfEq`）。 -/
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
