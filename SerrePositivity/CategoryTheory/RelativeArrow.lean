module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Relative pushout and pullback arrows of a natural transformation

A natural transformation A ⟶ B produces two functors on arrow categories:
the relative pushout A(y) ⨿_{A(x)} B(x) ⟶ B(y), and the relative pullback
A(x) ⟶ A(y) ×_{B(y)} B(x). The construction acts on all commutative squares,
so in particular preserves arrow isomorphisms and retract diagrams.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.RelativeArrow
variable {D : Type u} [Category.{v} D] {C : Type u'} [Category.{v'} C]
  {A B : D ⥤ C} (α : A ⟶ B)

section Pushout
variable [HasPushouts C]

abbrev pushoutArrow {x y : D} (f : x ⟶ y) :
    pushout (A.map f) (α.app x) ⟶ B.obj y :=
  pushout.desc (α.app y) (B.map f) (α.naturality f)

abbrev pushoutMap {f g : Arrow D} (s : f ⟶ g) :
    pushout (A.map f.hom) (α.app f.left) ⟶ pushout (A.map g.hom) (α.app g.left) :=
  pushout.map _ _ _ _ (A.map s.right) (B.map s.left) (A.map s.left)
    (by rw [← A.map_comp, ← A.map_comp, s.w]) (α.naturality s.left).symm

@[reassoc (attr := simp)]
lemma inl_pushoutMap {f g : Arrow D} (s : f ⟶ g) :
    pushout.inl _ _ ≫ pushoutMap α s = A.map s.right ≫ pushout.inl _ _ :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_pushoutMap {f g : Arrow D} (s : f ⟶ g) :
    pushout.inr _ _ ≫ pushoutMap α s = B.map s.left ≫ pushout.inr _ _ :=
  pushout.inr_desc _ _ _

lemma pushoutMap_square {f g : Arrow D} (s : f ⟶ g) :
    pushoutMap α s ≫ pushoutArrow α g.hom = pushoutArrow α f.hom ≫ B.map s.right := by
  apply pushout.hom_ext
  · rw [inl_pushoutMap_assoc, pushout.inl_desc, pushout.inl_desc_assoc]
    exact α.naturality s.right
  · rw [inr_pushoutMap_assoc, pushout.inr_desc, pushout.inr_desc_assoc]
    rw [← B.map_comp, ← B.map_comp, s.w]

lemma pushoutMap_id (f : Arrow D) : pushoutMap α (𝟙 f) = 𝟙 _ := by
  apply pushout.hom_ext
  · rw [inl_pushoutMap, Category.comp_id]
    change A.map (𝟙 f.right) ≫ pushout.inl _ _ = _
    rw [A.map_id, Category.id_comp]
  · rw [inr_pushoutMap, Category.comp_id]
    change B.map (𝟙 f.left) ≫ pushout.inr _ _ = _
    rw [B.map_id, Category.id_comp]

lemma pushoutMap_comp {f g h : Arrow D} (s : f ⟶ g) (t : g ⟶ h) :
    pushoutMap α (s ≫ t) = pushoutMap α s ≫ pushoutMap α t := by
  apply pushout.hom_ext
  · rw [inl_pushoutMap, inl_pushoutMap_assoc, inl_pushoutMap]
    change A.map (s.right ≫ t.right) ≫ pushout.inl _ _ = _
    rw [A.map_comp, Category.assoc]
  · rw [inr_pushoutMap, inr_pushoutMap_assoc, inr_pushoutMap]
    change B.map (s.left ≫ t.left) ≫ pushout.inr _ _ = _
    rw [B.map_comp, Category.assoc]

def pushoutFunctor : Arrow D ⥤ Arrow C where
  obj f := Arrow.mk (pushoutArrow α f.hom)
  map s := Arrow.homMk (pushoutMap α s) (B.map s.right) (pushoutMap_square α s)
  map_id f := by
    apply Arrow.hom_ext
    · exact pushoutMap_id α f
    · exact B.map_id f.right
  map_comp s t := by
    apply Arrow.hom_ext
    · exact pushoutMap_comp α s t
    · exact B.map_comp s.right t.right

end Pushout

section Pullback
variable [HasPullbacks C]

abbrev pullbackArrow {x y : D} (f : x ⟶ y) :
    A.obj x ⟶ pullback (α.app y) (B.map f) :=
  pullback.lift (A.map f) (α.app x) (α.naturality f)

abbrev pullbackMap {f g : Arrow D} (s : f ⟶ g) :
    pullback (α.app f.right) (B.map f.hom) ⟶ pullback (α.app g.right) (B.map g.hom) :=
  pullback.map _ _ _ _ (A.map s.right) (B.map s.left) (B.map s.right)
    (α.naturality s.right).symm (by rw [← B.map_comp, ← B.map_comp, s.w])

@[reassoc (attr := simp)]
lemma pullbackMap_fst {f g : Arrow D} (s : f ⟶ g) :
    pullbackMap α s ≫ pullback.fst _ _ = pullback.fst _ _ ≫ A.map s.right :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullbackMap_snd {f g : Arrow D} (s : f ⟶ g) :
    pullbackMap α s ≫ pullback.snd _ _ = pullback.snd _ _ ≫ B.map s.left :=
  pullback.lift_snd _ _ _

lemma pullbackMap_square {f g : Arrow D} (s : f ⟶ g) :
    A.map s.left ≫ pullbackArrow α g.hom = pullbackArrow α f.hom ≫ pullbackMap α s := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullbackMap_fst,
      ← Category.assoc, pullback.lift_fst]
    rw [← A.map_comp, ← A.map_comp, s.w]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullbackMap_snd,
      ← Category.assoc, pullback.lift_snd]
    exact α.naturality s.left

lemma pullbackMap_id (f : Arrow D) : pullbackMap α (𝟙 f) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [pullbackMap_fst, Category.id_comp]
    change pullback.fst _ _ ≫ A.map (𝟙 f.right) = _
    rw [A.map_id, Category.comp_id]
  · rw [pullbackMap_snd, Category.id_comp]
    change pullback.snd _ _ ≫ B.map (𝟙 f.left) = _
    rw [B.map_id, Category.comp_id]

lemma pullbackMap_comp {f g h : Arrow D} (s : f ⟶ g) (t : g ⟶ h) :
    pullbackMap α (s ≫ t) = pullbackMap α s ≫ pullbackMap α t := by
  apply pullback.hom_ext
  · rw [pullbackMap_fst, Category.assoc, pullbackMap_fst, ← Category.assoc, pullbackMap_fst]
    change pullback.fst _ _ ≫ A.map (s.right ≫ t.right) = _
    rw [A.map_comp, Category.assoc]
  · rw [pullbackMap_snd, Category.assoc, pullbackMap_snd, ← Category.assoc, pullbackMap_snd]
    change pullback.snd _ _ ≫ B.map (s.left ≫ t.left) = _
    rw [B.map_comp, Category.assoc]

def pullbackFunctor : Arrow D ⥤ Arrow C where
  obj f := Arrow.mk (pullbackArrow α f.hom)
  map s := Arrow.homMk (A.map s.left) (pullbackMap α s) (pullbackMap_square α s)
  map_id f := by
    apply Arrow.hom_ext
    · exact A.map_id f.left
    · exact pullbackMap_id α f
  map_comp s t := by
    apply Arrow.hom_ext
    · exact A.map_comp s.left t.left
    · exact pullbackMap_comp α s t

end Pullback
end SerrePositivity.RelativeArrow
