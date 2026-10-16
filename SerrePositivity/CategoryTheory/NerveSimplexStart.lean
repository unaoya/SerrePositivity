module

public import SerrePositivity.CategoryTheory.NerveSimplexEndpoint

/-! # Contravariant first endpoint on the actual nerve simplex category -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.NerveSimplexStart
variable {D : Type u} [Category.{v} D]

abbrev start (s : Index D) : D := (chain s).obj 0

/-- The actual initialSegment from the larger chain's first vertex to the reindexed first vertex. -/
def initialSegment {n m : ℕ} (c : Fin (n + 1) ⥤ D) (d : Fin (m + 1) ⥤ D)
    (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (h : (SimplexCategory.toCat.map θ).toFunctor ⋙ d = c) : d.obj 0 ⟶ c.obj 0 :=
  d.map (homOfLE (Fin.zero_le (θ.toOrderHom 0))) ≫
    eqToHom (congrArg (fun q : Fin (n + 1) ⥤ D => q.obj 0) h)

lemma prefix_comp {n m k : ℕ} (c : Fin (n + 1) ⥤ D) (d : Fin (m + 1) ⥤ D)
    (e : Fin (k + 1) ⥤ D) (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (ψ : SimplexCategory.mk m ⟶ SimplexCategory.mk k)
    (hθ : (SimplexCategory.toCat.map θ).toFunctor ⋙ d = c)
    (hψ : (SimplexCategory.toCat.map ψ).toFunctor ⋙ e = d)
    (h : (SimplexCategory.toCat.map (θ ≫ ψ)).toFunctor ⋙ e = c) :
    initialSegment c e (θ ≫ ψ) h = initialSegment d e ψ hψ ≫ initialSegment c d θ hθ := by
  subst c
  subst d
  simp only [initialSegment, eqToHom_refl, Category.comp_id]
  exact e.map_comp _ _

def startMap {s t : Index D} (f : s ⟶ t) : start t ⟶ start s :=
  initialSegment (chain s) (chain t) (operator f) (chain_eq f)

lemma startMap_id (s : Index D) : startMap (𝟙 s) = 𝟙 (start s) := by
  simp [startMap, initialSegment]

lemma startMap_comp {s t r : Index D} (f : s ⟶ t) (g : t ⟶ r) :
    startMap (f ≫ g) = startMap g ≫ startMap f :=
  prefix_comp (chain s) (chain t) (chain r) (operator f) (operator g)
    (chain_eq f) (chain_eq g) (chain_eq (f ≫ g))

def functor (D : Type u) [Category.{v} D] : Index D ⥤ Dᵒᵖ where
  obj s := Opposite.op (start s)
  map f := (startMap f).op
  map_id s := congrArg Quiver.Hom.op (startMap_id s)
  map_comp f g := congrArg Quiver.Hom.op (startMap_comp f g)

lemma reindexArrow_start {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    startMap (reindexArrow c θ) = c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0))) := by
  simp only [startMap, initialSegment, eqToHom_refl, Category.comp_id]

end SerrePositivity.NerveSimplexStart
