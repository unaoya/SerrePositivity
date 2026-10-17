module
public import Mathlib.CategoryTheory.Functor.Currying

/-! # dg合成の自然性に使用するパラメータ付き関手合成 -/
@[expose] public section
noncomputable section
universe u₀ u₁ u₂ u₃ u₄ v₀ v₁ v₂ v₃ v₄
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable {T : Type u₀} [Category.{v₀} T] {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]

def compositionFamily (F : T ⥤ C ⥤ D) (G : T ⥤ D ⥤ E) : T ⥤ C ⥤ E :=
  F.prod' G ⋙ uncurry.obj (whiskeringLeft C D E)

def compositionFamilyMap {F F' : T ⥤ C ⥤ D} {G G' : T ⥤ D ⥤ E}
    (a : F ⟶ F') (b : G ⟶ G') : compositionFamily F G ⟶ compositionFamily F' G' :=
  whiskerRight (NatTrans.prod' a b) (uncurry.obj (whiskeringLeft C D E))

variable {H : Type u₄} [Category.{v₄} H]

def compositionFamilyAssociator (F : T ⥤ C ⥤ D) (G : T ⥤ D ⥤ E)
    (K : T ⥤ E ⥤ H) :
    compositionFamily (compositionFamily F G) K ≅ compositionFamily F (compositionFamily G K) :=
  NatIso.ofComponents (fun t => Functor.associator (F.obj t) (G.obj t) (K.obj t))
    (fun f => by
      ext X
      dsimp [compositionFamily, uncurry, whiskeringLeft, whiskerLeft]
      simp only [CategoryTheory.Functor.map_comp, Category.id_comp, Category.comp_id,
        Category.assoc])

end SerrePositivity.DifferentialGraded.BimoduleTensor
