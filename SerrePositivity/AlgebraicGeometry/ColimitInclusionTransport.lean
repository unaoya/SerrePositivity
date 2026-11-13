module

public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：余極限比較が標準写像を保つ性質の、合成と自然同型による移送。
方針：関手の合成則、自然性、colimit.ι_map を使う。
規約：比較同型と標準写像への公式を明示的に指定する。
使われ方：整数係数の Čech H の ULift による比較の標準写像との整合性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe v u v₁ u₁ v₂ u₂ v₃ u₃
variable {J : Type u} [Category.{v} J]
variable {C : Type u₁} [Category.{v₁} C] {A : Type u₂} [Category.{v₂} A]
variable {B : Type u₃} [Category.{v₃} B]

/-- 標準写像を保つ二つの比較の合成も標準写像を保つ。 -/
theorem colimitInclusion_composition (D : J ⥤ C) (F : C ⥤ A) (G : A ⥤ B)
    [HasColimit D] [HasColimit (D ⋙ F)] [HasColimit ((D ⋙ F) ⋙ G)]
    (e : F.obj (colimit D) ≅ colimit (D ⋙ F))
    (d : G.obj (colimit (D ⋙ F)) ≅ colimit ((D ⋙ F) ⋙ G))
    (he : ∀ j, F.map (colimit.ι D j) ≫ e.hom = colimit.ι (D ⋙ F) j)
    (hd : ∀ j, G.map (colimit.ι (D ⋙ F) j) ≫ d.hom = colimit.ι ((D ⋙ F) ⋙ G) j)
    (j : J) :
    (F ⋙ G).map (colimit.ι D j) ≫ (G.mapIso e ≪≫ d).hom =
      colimit.ι ((D ⋙ F) ⋙ G) j := by
  change G.map (F.map (colimit.ι D j)) ≫ (G.map e.hom ≫ d.hom) = _
  rw [← G.map_comp_assoc, he, hd]

/-- 自然同型で移した比較も、同じ標準写像を保つ。 -/
theorem colimitInclusion_natIso (D : J ⥤ C) {F G : C ⥤ A}
    [HasColimit D] [HasColimitsOfShape J A]
    (e : F ≅ G) (d : G.obj (colimit D) ≅ colimit (D ⋙ G))
    (hd : ∀ j, G.map (colimit.ι D j) ≫ d.hom = colimit.ι (D ⋙ G) j) (j : J) :
    F.map (colimit.ι D j) ≫
      (e.app (colimit D) ≪≫ d ≪≫ colim.mapIso (isoWhiskerLeft D e).symm).hom =
      colimit.ι (D ⋙ F) j := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  change F.map (colimit.ι D j) ≫
    (e.hom.app (colimit D) ≫ d.hom ≫ colim.map (isoWhiskerLeft D e).inv) = _
  rw [← Category.assoc, e.hom.naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (G.map (colimit.ι D j)), hd, colimit.ι_map]
  change (e.app (D.obj j)).hom ≫ (e.app (D.obj j)).inv ≫ colimit.ι (D ⋙ F) j = _
  rw [Iso.hom_inv_id_assoc]

end SerrePositivity.AlgebraicGeometry
