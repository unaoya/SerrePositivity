module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiscreteKanExtension

/-! # Unique discrete-valued descent through every localized equivalence

This applies to quotient projections as well as anodyne units. No model
structure or smallness of the base category is required.
-/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.DiscreteLocalizedExtension
open PiZeroConstant
variable {A B : SSet.{w}} (i : A ⟶ B)
  (hi : IsIso (AnodyneHomotopy.anodyneQ.map i)) {T : Type w}

include hi in
lemma pre_bijective : Function.Bijective (fun g : B ⟶ discrete T => i ≫ g) := by
  have ht := KanTestDetection.tests_of_anodyneQ_isIso i hi _ (discrete_terminal_rlp T)
  constructor
  · intro f g h
    apply homEquiv.injective
    have hc : HomotopyClasses.mk f = HomotopyClasses.mk g :=
      ht.injective (congrArg HomotopyClasses.mk h)
    exact congrArg PiZeroLocalization.classEquiv hc
  · intro f
    obtain ⟨c, hc⟩ := ht.surjective (HomotopyClasses.mk f)
    obtain ⟨g, rfl⟩ := Quot.exists_rep c
    refine ⟨g, homEquiv.injective ?_⟩
    exact congrArg PiZeroLocalization.classEquiv hc

def extension (f : A ⟶ discrete T) : B ⟶ discrete T :=
  ((pre_bijective i hi).surjective f).choose

lemma extension_fac (f : A ⟶ discrete T) : i ≫ extension i hi f = f :=
  ((pre_bijective i hi).surjective f).choose_spec

lemma extension_unique (f : A ⟶ discrete T) (g : B ⟶ discrete T) (hg : i ≫ g = f) :
    g = extension i hi f := (pre_bijective i hi).injective
  (hg.trans (extension_fac i hi f).symm)

variable {D : Type uD} [Category.{vD} D] {F G : D ⥤ SSet.{w}} {T : D ⥤ Type w}
  (p : F ⟶ G) (hp : ∀ d, IsIso (AnodyneHomotopy.anodyneQ.map (p.app d)))
  (a : F ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ)

def descend : G ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ where
  app d := extension (p.app d) (hp d) (a.app d)
  naturality {d e} f := by
    apply (pre_bijective (p.app d) (hp d)).injective
    change p.app d ≫ (G.map f ≫ _) = p.app d ≫ (_ ≫ _)
    rw [← Category.assoc, ← p.naturality, Category.assoc,
      extension_fac, ← Category.assoc, extension_fac]
    exact a.naturality f

lemma descend_fac : p ≫ descend p hp a = a := by
  apply NatTrans.ext
  funext d
  exact extension_fac _ (hp d) (a.app d)

lemma descend_unique (b : G ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ) (hb : p ≫ b = a) :
    b = descend p hp a := by
  apply NatTrans.ext
  funext d
  exact extension_unique _ (hp d) (a.app d) (b.app d) (congr_app hb d)

end SerrePositivity.SimplicialModel.DiscreteLocalizedExtension
