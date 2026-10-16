module

public import SerrePositivity.CategoryTheory.ArrowFactorizationTransport
public import SerrePositivity.CategoryTheory.AnchoredChainNerve

/-! # Strict external transport of the entire simplicial chain parameter

Functorial maps of factorization categories are sent through the nerve
isomorphism. All ordinal operators, identities and composites are handled
simultaneously. The finite-degree formula retains the actual middle diagram.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.AnchoredChain
variable {D : Type u} [Category.{v} D] {Y V Y' V' : D}
  {g : Y ⟶ V} {h : Y' ⟶ V'}

def mapFunctor (F : ArrowFactorization g ⥤ ArrowFactorization h) : simplicial g ⟶ simplicial h :=
  (nerveIso g).inv ≫ nerveMap F ≫ (nerveIso h).hom

lemma mapFunctor_id : mapFunctor (𝟭 (ArrowFactorization g)) = 𝟙 (simplicial g) := by
  change (nerveIso g).inv ≫ (𝟙 _) ≫ (nerveIso g).hom = _
  rw [Category.id_comp, Iso.inv_hom_id]

lemma mapFunctor_comp {Y'' V'' : D} {k : Y'' ⟶ V''}
    (F : ArrowFactorization g ⥤ ArrowFactorization h)
    (G : ArrowFactorization h ⥤ ArrowFactorization k) :
    mapFunctor F ≫ mapFunctor G = mapFunctor (F ⋙ G) := by
  calc
    _ = (nerveIso g).inv ≫ nerveMap F ≫ nerveMap G ≫ (nerveIso k).hom := by
      simp only [mapFunctor, Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := rfl

@[reassoc]
lemma fromNerve_mapFunctor (F : ArrowFactorization g ⥤ ArrowFactorization h) :
    (nerveIso g).hom ≫ mapFunctor F = nerveMap F ≫ (nerveIso h).hom := by
  simp only [mapFunctor, Iso.hom_inv_id_assoc]

lemma mapFunctor_degree (F : ArrowFactorization g ⥤ ArrowFactorization h) {n : ℕ}
    (c : AnchoredChain g n) :
    (mapFunctor F).app (Opposite.op (SimplexCategory.mk n)) c =
      fromDiagram (cutDiagram c ⋙ F) := by
  have hc := congrArg (fun q => q.app (Opposite.op (SimplexCategory.mk n)) (cutDiagram c))
    (fromNerve_mapFunctor F)
  change (mapFunctor F).app (Opposite.op (SimplexCategory.mk n)) (fromDiagram (cutDiagram c)) =
    fromDiagram (cutDiagram c ⋙ F) at hc
  rw [fromDiagram_cutDiagram] at hc
  exact hc

lemma mapFunctor_cut (F : ArrowFactorization g ⥤ ArrowFactorization h) {n : ℕ}
    (c : AnchoredChain g n) (j : Fin (n + 1)) :
    ((mapFunctor F).app (Opposite.op (SimplexCategory.mk n)) c).cut j = F.obj (c.cut j) := by
  rw [mapFunctor_degree]
  exact cutDiagram_fromDiagram_obj (cutDiagram c ⋙ F) j

abbrev transport (g : Y ⟶ V) (a : Y' ⟶ Y) (b : V ⟶ V') (h : Y' ⟶ V')
    (e : (a ≫ g) ≫ b = h) : simplicial g ⟶ simplicial h :=
  mapFunctor (ArrowFactorization.transport g a b h e)

lemma transport_id (g : Y ⟶ V) :
    transport g (𝟙 Y) (𝟙 V) g (by simp) = 𝟙 (simplicial g) := by
  rw [transport, ArrowFactorization.transport_id, mapFunctor_id]

lemma transport_comp {Y'' V'' : D} (g : Y ⟶ V) (a : Y' ⟶ Y) (b : V ⟶ V') (h : Y' ⟶ V')
    (e : (a ≫ g) ≫ b = h) (a' : Y'' ⟶ Y') (b' : V' ⟶ V'') (k : Y'' ⟶ V'')
    (e' : (a' ≫ h) ≫ b' = k) :
    transport g a b h e ≫ transport h a' b' k e' =
      transport g (a' ≫ a) (b ≫ b') k (ArrowFactorization.context_comp g a b h e a' b' k e') := by
  exact (mapFunctor_comp _ _).trans
    (congrArg (fun F : ArrowFactorization g ⥤ ArrowFactorization k => mapFunctor F)
      (ArrowFactorization.transport_comp g a b h e a' b' k e'))

lemma transport_diagram (g : Y ⟶ V) (a : Y' ⟶ Y) (b : V ⟶ V') (h : Y' ⟶ V')
    (e : (a ≫ g) ≫ b = h) {n : ℕ} (c : AnchoredChain g n) :
    ((transport g a b h e).app (Opposite.op (SimplexCategory.mk n)) c).diagram = c.diagram := by
  rw [transport, mapFunctor_degree]
  change (cutDiagram c ⋙ ArrowFactorization.transport g a b h e) ⋙
    ArrowFactorization.forget h = _
  rw [CategoryTheory.Functor.assoc, ArrowFactorization.transport_forget]
  rfl

lemma mapFunctor_pre_post (g : Y ⟶ V) (a : Y' ⟶ Y) (b : V ⟶ V') (h : Y' ⟶ V')
    (e : (a ≫ g) ≫ b = h) :
    mapFunctor (ArrowFactorization.preTo g a (a ≫ g) rfl) ≫
      mapFunctor (ArrowFactorization.postTo (a ≫ g) b h e) =
    mapFunctor (ArrowFactorization.postTo g b (g ≫ b) rfl) ≫
      mapFunctor (ArrowFactorization.preTo (g ≫ b) a h ((Category.assoc a g b).symm.trans e)) := by
  exact (mapFunctor_comp _ _).trans
    ((congrArg (fun F : ArrowFactorization g ⥤ ArrowFactorization h => mapFunctor F)
      (ArrowFactorization.pre_post g a b h e)).trans (mapFunctor_comp _ _).symm)

end SerrePositivity.AnchoredChain
