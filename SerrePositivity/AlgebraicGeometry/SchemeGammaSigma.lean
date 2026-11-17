module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
概要：同じスキームの余積の大域切断を、元の入射を保って積へ移す。
方針：反対圏の余積と積の標準同型と、Γ の極限保存を合成する。
規約：元の族と入射、族の写像の自然性を保持する。
使われ方：有限アフィン族の nerve と同じ矩形タプルの係数の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {ι : Type} (Z : ι → Scheme.{u})

/-- 元の余積の各入射を射影に持つ、大域切断の標準同型。 -/
def schemeGammaSigmaIso : Scheme.Γ.obj (op (∐ Z)) ≅ ∏ᶜ (fun i ↦ Scheme.Γ.obj (op (Z i))) :=
  Scheme.Γ.mapIso (opCoproductIsoProduct Z) ≪≫
    PreservesProduct.iso Scheme.Γ (fun i ↦ op (Z i))

set_option backward.isDefEq.respectTransparency false in
/-- 同じ標準同型の射影は、元の余積入射の Γ。 -/
theorem schemeGammaSigmaIso_π (i : ι) :
    (schemeGammaSigmaIso Z).hom ≫ Pi.π (fun i ↦ Scheme.Γ.obj (op (Z i))) i =
      Scheme.Γ.map (Sigma.ι Z i).op := by
  rw [schemeGammaSigmaIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc, PreservesProduct.iso_hom,
    piComparison_comp_π, ← Scheme.Γ.map_comp, opCoproductIsoProduct_hom_comp_π]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ余積射の Γ は、元の各成分の Γ を同じ積への射として持つ。 -/
theorem schemeGammaSigmaIso_desc {S : Scheme.{u}} (f : ∀ i, Z i ⟶ S) :
    Scheme.Γ.map (CategoryTheory.Limits.Sigma.desc f).op ≫ (schemeGammaSigmaIso Z).hom =
      Pi.lift (fun i ↦ Scheme.Γ.map (f i).op) := by
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, schemeGammaSigmaIso_π, Pi.lift_comp_π,
    ← Scheme.Γ.map_comp, ← CategoryTheory.op_comp, Sigma.ι_comp_desc]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ切断の標準比較は、元の族の写像に自然。 -/
theorem schemeGammaSigmaIso_naturality {W : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ W i) :
    Scheme.Γ.map (CategoryTheory.Limits.Sigma.map f).op ≫ (schemeGammaSigmaIso Z).hom =
      (schemeGammaSigmaIso W).hom ≫ CategoryTheory.Limits.Pi.map (fun i ↦ Scheme.Γ.map (f i).op) := by
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, schemeGammaSigmaIso_π, Category.assoc, CategoryTheory.Limits.Pi.map_π,
    ← Category.assoc, schemeGammaSigmaIso_π]
  rw [← Scheme.Γ.map_comp, ← Scheme.Γ.map_comp, ← CategoryTheory.op_comp,
    ← CategoryTheory.op_comp, CategoryTheory.Limits.Sigma.ι_map]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ標準比較は、添字を変える元の成分の射にも自然。 -/
theorem schemeGammaSigmaIso_reindex_naturality {κ : Type} {W : κ → Scheme.{u}}
    (ρ : ι → κ) (f : ∀ i, Z i ⟶ W (ρ i)) :
    Scheme.Γ.map (Sigma.desc (fun i ↦ f i ≫ Sigma.ι W (ρ i))).op ≫
        (schemeGammaSigmaIso Z).hom =
      (schemeGammaSigmaIso W).hom ≫ Pi.lift
        (fun i ↦ Pi.π (fun j ↦ Scheme.Γ.obj (op (W j))) (ρ i) ≫ Scheme.Γ.map (f i).op) := by
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, schemeGammaSigmaIso_π, Category.assoc, Pi.lift_comp_π,
    ← Category.assoc, schemeGammaSigmaIso_π]
  rw [← Scheme.Γ.map_comp, ← Scheme.Γ.map_comp, ← CategoryTheory.op_comp,
    ← CategoryTheory.op_comp, Sigma.ι_comp_desc]

end SerrePositivity.AlgebraicGeometry
