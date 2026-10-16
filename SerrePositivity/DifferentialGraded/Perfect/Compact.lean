module
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableCoproductSupport

/-! # u-small余積に関するdg導来加群のcompact性

加法圏でのcompact性を、余積への射が有限個の包含の像の和となる条件で表す。
余積の添字宇宙はuであり、主導来圏の対象宇宙をsmallと仮定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleCompact : ObjectProperty (DerivedModuleCategory A D) := fun X =>
  ∀ (J : Type u) (F : J → DerivedModuleCategory A D) (f : X ⟶ ∐ F),
    ∃ (t : Finset J) (g : ∀ j, X ⟶ F j), ∑ j ∈ t, g j ≫ Sigma.ι F j = f

/-- 代表加群は、任意のu-smallな主導来対象族に対してcompact。 -/
lemma moduleRepresentable_compact (x : D) :
    moduleCompact A D ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))) := by
  classical
  intro J F f
  let R := fun j => moduleCanonicalProjectiveResolution A D (F j).as.obj
  let P := fun j => (R j).obj
  let e (j : J) : (moduleToDerived A D).obj (P j) ≅ F j :=
    moduleDerivedIso A D (R j).π (R j).quasiIso
  let s : Cofan (fun j => (moduleToDerived A D).obj (P j)) :=
    Cofan.mk (∐ F) (fun j => (e j).hom ≫ Sigma.ι F j)
  let k := moduleProjectiveDerivedCofanDesc A D P (fun j => (R j).projective) s
  let l : (∐ F) ⟶ (moduleToDerived A D).obj (∐ P) :=
    Sigma.desc (fun j => (e j).inv ≫ (moduleToDerived A D).map (Sigma.ι P j))
  have hk (j : J) : (moduleToDerived A D).map (Sigma.ι P j) ≫ k =
      (e j).hom ≫ Sigma.ι F j :=
    moduleProjectiveDerivedCofanDesc_fac A D P (fun j => (R j).projective) s j
  have hlk : l ≫ k = 𝟙 (∐ F) := by
    apply Sigma.hom_ext
    intro j
    simp only [l, Sigma.ι_comp_desc_assoc, hk, Category.assoc,
      Iso.inv_hom_id_assoc, Category.comp_id]
  obtain ⟨t, g, hg⟩ := moduleRepresentableDerivedCoproduct_rep A D x P (f ≫ l)
  refine ⟨t, fun j => g j ≫ (e j).hom, ?_⟩
  calc
    _ = ∑ j ∈ t, (g j ≫ (moduleToDerived A D).map (Sigma.ι P j)) ≫ k := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Category.assoc, hk]
    _ = (∑ j ∈ t, g j ≫ (moduleToDerived A D).map (Sigma.ι P j)) ≫ k :=
      (sum_comp _ _ _).symm
    _ = f := by rw [hg, Category.assoc, hlk, Category.comp_id]

end SerrePositivity.DifferentialGraded
