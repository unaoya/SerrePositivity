module
public import SerrePositivity.DifferentialGraded.Module.ClosedMaps

/-! # 全次数自然な複体同型族からの加群同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 全次数自然な同型族の逆も全次数自然。 -/
lemma moduleIsoFamily_inv_naturality {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ≅ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y).hom =
      N.map x y ≫ homPrecompose (a x).hom (N.obj y)) (x y : Dᵒᵖ) :
    N.map x y ≫ homPostcompose (N.obj x) (a y).inv =
      M.map x y ≫ homPrecompose (a x).inv (M.obj y) := by
  apply closedFamily_of_action A (M := N) (N := M) (fun x => (a x).inv)
  intro x y p r n hn f v
  have hh := closedFamily_action A (fun x => (a x).hom) h x y p r n hn f ((a x).inv.f r v)
  have hi := congrArg (fun t => (a y).inv.f n t) hh
  simp only [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
    Iso.hom_inv_id, Iso.inv_hom_id, HomologicalComplex.id_f, ModuleCat.id_apply] at hi
  exact hi.symm

variable (D) [Small.{u} D]

/-- 全次数自然な同型族を主 Hom end の閉零加群同型へ持ち上げる。 -/
def moduleIsoMk {M N : RightModule A D} (a : ∀ x : Dᵒᵖ, M.obj x ≅ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y).hom =
      N.map x y ≫ homPrecompose (a x).hom (N.obj y)) :
    ForgetEnrichment.of (Complex A) M ≅ ForgetEnrichment.of (Complex A) N where
  hom := moduleMorphismMk A D (fun x => (a x).hom) h
  inv := moduleMorphismMk A D (fun x => (a x).inv) (moduleIsoFamily_inv_naturality A a h)
  hom_inv_id := by
    apply moduleMorphism_ext
    intro x
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      moduleMorphismMk_eval, moduleMorphismMk_eval]
    exact (a (op x)).hom_inv_id
  inv_hom_id := by
    apply moduleMorphism_ext
    intro x
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      moduleMorphismMk_eval, moduleMorphismMk_eval]
    exact (a (op x)).inv_hom_id

@[simp] lemma moduleIsoMk_hom_eval {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ≅ N.obj x) (h) (x : D) :
    (moduleEvaluation A D x).map (moduleIsoMk A D a h).hom = (a (op x)).hom :=
  moduleMorphismMk_eval A D _ _ x

@[simp] lemma moduleIsoMk_inv_eval {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ≅ N.obj x) (h) (x : D) :
    (moduleEvaluation A D x).map (moduleIsoMk A D a h).inv = (a (op x)).inv :=
  moduleMorphismMk_eval A D _ _ x
end SerrePositivity.DifferentialGraded
