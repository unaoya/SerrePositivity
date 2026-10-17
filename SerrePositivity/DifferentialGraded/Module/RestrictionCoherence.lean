module
public import SerrePositivity.DifferentialGraded.Module.Restriction
public import SerrePositivity.DifferentialGraded.Module.Isomorphism
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation

/-! # dg加群制限の恒等・合成比較

比較の評価成分は恒等chain mapで、全Hom自然性は豊穣関手の結合則から得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleRestrictionIdObjIso (M : ModuleCategory A D) :
    (moduleRestriction A D D (DGFunctor.id Dᵒᵖ)).obj M ≅ M :=
  moduleIsoMk A D
    (M := restrictModule A D D (DGFunctor.id Dᵒᵖ) (ForgetEnrichment.to (Complex A) M))
    (N := ForgetEnrichment.to (Complex A) M) (fun _ => Iso.refl _) (by
    intro x y
    apply hom_naturality_of_apply
    intro p f
    simp only [Iso.refl_hom, Cochain.comp_id, Cochain.id_comp]
    change (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) M).map x y).f p f = _
    rw [Category.id_comp])

@[simp] lemma moduleRestrictionIdObjIso_hom_eval (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleRestrictionIdObjIso A D M).hom = 𝟙 _ :=
  moduleIsoMk_hom_eval A D _ _ x

def moduleRestrictionIdIso : moduleRestriction A D D (DGFunctor.id Dᵒᵖ) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (F := moduleRestriction A D D (DGFunctor.id Dᵒᵖ)) (G := 𝟭 (ModuleCategory A D))
    (moduleRestrictionIdObjIso A D) (by
    intro M N f
    apply moduleMorphism_ext
    intro x
    simp only [Functor.id_map, Functor.map_comp, moduleRestrictionIdObjIso,
      moduleIsoMk_hom_eval, moduleRestriction_map_eval]
    rfl)

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type z) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A Dᵒᵖ Eᵒᵖ) (G : DGFunctor A Eᵒᵖ Tᵒᵖ)

def moduleRestrictionCompObjIso (M : ModuleCategory A T) :
    (moduleRestriction A D E F).obj ((moduleRestriction A E T G).obj M) ≅
      (moduleRestriction A D T (F.comp G)).obj M :=
  moduleIsoMk A D
    (M := restrictModule A D E F
      (restrictModule A E T G (ForgetEnrichment.to (Complex A) M)))
    (N := restrictModule A D T (F.comp G) (ForgetEnrichment.to (Complex A) M))
    (fun _ => Iso.refl _) (by
    intro x y
    apply hom_naturality_of_apply
    intro p f
    simp only [Iso.refl_hom, Cochain.comp_id, Cochain.id_comp]
    change (F.map x y ≫ (G.map (F.obj x) (F.obj y) ≫
      (ForgetEnrichment.to (Complex A) M).map (G.obj (F.obj x)) (G.obj (F.obj y)))).f p f =
      ((F.map x y ≫ G.map (F.obj x) (F.obj y)) ≫
        (ForgetEnrichment.to (Complex A) M).map (G.obj (F.obj x)) (G.obj (F.obj y))).f p f
    rw [Category.assoc])

@[simp] lemma moduleRestrictionCompObjIso_hom_eval (M : ModuleCategory A T) (x : D) :
    (moduleEvaluation A D x).map (moduleRestrictionCompObjIso A D E T F G M).hom = 𝟙 _ :=
  moduleIsoMk_hom_eval A D _ _ x

def moduleRestrictionCompIso :
    moduleRestriction A E T G ⋙ moduleRestriction A D E F ≅
      moduleRestriction A D T (F.comp G) :=
  NatIso.ofComponents
    (F := moduleRestriction A E T G ⋙ moduleRestriction A D E F)
    (G := moduleRestriction A D T (F.comp G))
    (moduleRestrictionCompObjIso A D E T F G) (by
    intro M N f
    apply moduleMorphism_ext
    intro x
    simp only [Functor.comp_map, Functor.map_comp,
      moduleRestrictionCompObjIso_hom_eval,
      moduleRestriction_map_eval]
    rfl)

end SerrePositivity.DifferentialGraded
