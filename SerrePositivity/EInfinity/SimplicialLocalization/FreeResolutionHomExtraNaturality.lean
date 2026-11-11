module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionHomExtra

/-!
# 一文字の追加退化と元の全作用素の整合性

概要：追加退化と全ての正の面・退化の交換則を証明する。
方針：自由関手の一文字の列への作用と元の端点移送を照合する。
規約：元の作用素・augmentation と同じ射を保持する。
使われ方：元の自由 Hom の追加退化と収縮。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Opposite SerrePositivity.HomotopyFunctionComplex.ComonadResolutionOperators
open scoped Simplicial

lemma singlePath_conjugate_heq {V : Type u} [Category.{u} V] {A A' B B' : V}
    (hA : A' = A) (hB : B = B') (f : A ⟶ B) :
    HEq (Quiver.Hom.toPath (V := V) (eqToHom hA ≫ f ≫ eqToHom hB))
      (Quiver.Hom.toPath (V := V) f) := by
  cases hA
  cases hB
  simp

lemma singlePath_map_heq {V W : Type u} [Category.{u} V] [Category.{u} W]
    (F G : V ⥤ W) (h : F = G) {A B : V} (f : A ⟶ B) :
    HEq (Quiver.Hom.toPath (V := W) (F.map f))
      (Quiver.Hom.toPath (V := W) (G.map f)) := by
  cases h
  rfl

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category}

lemma generatorHomExtra_face_lift_heq (n : ℕ) (i : Fin (n + 2))
    (f : (freeResolutionGeneratorHom C X Y) _⦋n + 1⦌) :
    HEq (generatorHomExtra C n ((freeResolutionGeneratorHom C X Y).δ i f))
      (Quiver.Hom.toPath (V := (power _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 1)).category)
        ((face _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 1) i).functor.map f)) := by
  change HEq (Quiver.Hom.toPath (V := (power _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 1)).category)
    (eqToHom _ ≫ ((freeResolution C).δ i).functor.map f ≫ eqToHom _)) _
  have h := singlePath_conjugate_heq
    (freeResolutionHomObject_naturality C (SimplexCategory.δ i).op X).symm
    (freeResolutionHomObject_naturality C (SimplexCategory.δ i).op Y)
    (((freeResolution C).δ i).functor.map f)
  refine h.trans ?_
  exact singlePath_map_heq _ _ (congrArg LocalizerMorphism.functor
    (freeResolution_face C i)) f

lemma generatorHomExtra_degeneracy_lift_heq (n : ℕ) (i : Fin (n + 1))
    (f : (freeResolutionGeneratorHom C X Y) _⦋n⦌) :
    HEq (generatorHomExtra C (n + 1) ((freeResolutionGeneratorHom C X Y).σ i f))
      (Quiver.Hom.toPath (V := (power _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 2)).category)
        ((degeneracy _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C n i).functor.map f)) := by
  change HEq (Quiver.Hom.toPath (V := (power _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 2)).category)
    (eqToHom _ ≫ ((freeResolution C).σ i).functor.map f ≫ eqToHom _)) _
  have h := singlePath_conjugate_heq
    (freeResolutionHomObject_naturality C (SimplexCategory.σ i).op X).symm
    (freeResolutionHomObject_naturality C (SimplexCategory.σ i).op Y)
    (((freeResolution C).σ i).functor.map f)
  refine h.trans ?_
  exact singlePath_map_heq _ _ (congrArg LocalizerMorphism.functor
    (freeResolution_degeneracy C i)) f

lemma generatorHomSection_augmentation_lift_heq
    (f : (freeResolutionGeneratorHom C X Y) _⦋0⦌) :
    HEq (generatorHomSection C ((freeResolutionGeneratorHomAugmentation C X Y).app (op ⦋0⦌) f))
      (Quiver.Hom.toPath (V := C.category) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit C.weakEquivalences).functor.map f)) := by
  change HEq (Quiver.Hom.toPath (V := C.category)
    (eqToHom _ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit C.weakEquivalences).functor.map f) ≫ eqToHom _)) _
  exact singlePath_conjugate_heq _ _ _

lemma generatorHomExtra_face_succ (n : ℕ) (i : Fin (n + 2))
    (f : (freeResolutionGeneratorHom C X Y) _⦋n + 1⦌) :
    (freeResolutionGeneratorHom C X Y).δ i.succ (generatorHomExtra C (n + 1) f) =
      generatorHomExtra C n ((freeResolutionGeneratorHom C X Y).δ i f) := by
  apply eq_of_heq
  have h := generatorHom_face_heq C (n + 1) i.succ (generatorHomExtra C (n + 1) f)
  rw [face_succ] at h
  exact h.trans ((heq_of_eq (Prefunctor.mapPath_toPath _ f)).trans
    (generatorHomExtra_face_lift_heq C n i f).symm)

lemma generatorHomExtra_degeneracy_succ (n : ℕ) (i : Fin (n + 1))
    (f : (freeResolutionGeneratorHom C X Y) _⦋n⦌) :
    (freeResolutionGeneratorHom C X Y).σ i.succ (generatorHomExtra C n f) =
      generatorHomExtra C (n + 1) ((freeResolutionGeneratorHom C X Y).σ i f) := by
  apply eq_of_heq
  have h := generatorHom_degeneracy_heq C (n + 1) i.succ (generatorHomExtra C n f)
  rw [degeneracy_succ] at h
  exact h.trans ((heq_of_eq (Prefunctor.mapPath_toPath _ f)).trans
    (generatorHomExtra_degeneracy_lift_heq C n i f).symm)

lemma generatorHomExtra_face_one (f : (freeResolutionGeneratorHom C X Y) _⦋0⦌) :
    (freeResolutionGeneratorHom C X Y).δ (1 : Fin 2) (generatorHomExtra C 0 f) =
      generatorHomSection C ((freeResolutionGeneratorHomAugmentation C X Y).app (op ⦋0⦌) f) := by
  apply eq_of_heq
  have h := generatorHom_face_heq C 0 (1 : Fin 2) (generatorHomExtra C 0 f)
  change HEq _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit C.weakEquivalences)).functor.map
    (Quiver.Hom.toPath (V := (power _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C 1).category) f)) at h
  exact h.trans ((heq_of_eq (Prefunctor.mapPath_toPath _ f)).trans
    (generatorHomSection_augmentation_lift_heq C f).symm)

end SerrePositivity.EInfinity.SimplicialLocalization
