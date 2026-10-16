module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoPushoutEquivalence

/-! # Model-free left properness of the original anodyne localization

Every localized equivalence remains one after an actual pushout along a
mono. Boundary factorization reduces to the mono and boundary-right cases.
Neither the comparing map nor any original object is assumed Kan.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.KanLocalizedLeftProper
open MonoLocalizedFactorization
variable {A B C P : SSet.{v}} (f : A ⟶ B)
  (hf : IsIso (AnodyneHomotopy.anodyneQ.map f))
  (j : A ⟶ C) [Mono j] (u : B ⟶ P) (g : C ⟶ P) (sq : IsPushout f j u g)

include hf sq in
lemma localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map g) := by
  let i := left f
  let p := right f
  let u₁ := pushout.inl i j
  let g₁ := pushout.inr i j
  have hm : Mono u₁ := (MorphismProperty.monomorphisms SSet.{v}).pushout_inl i j inferInstance
  let t := pushout.desc (f := i) (g := j) (p ≫ u) g (by
    rw [← Category.assoc, fac]
    exact sq.w)
  have hu : u₁ ≫ t = p ≫ u := pushout.inl_desc _ _ _
  have hg : g₁ ≫ t = g := pushout.inr_desc _ _ _
  have ho : IsPushout (i ≫ p) j u (g₁ ≫ t) := by
    rw [hg, fac]
    exact sq
  have hs : IsPushout p u₁ u t := ho.of_left hu.symm (IsPushout.of_hasPushout i j)
  have h₁ : IsIso (AnodyneHomotopy.anodyneQ.map g₁) :=
    KanMonoPushoutEquivalence.localized_isIso i j u₁ g₁ (IsPushout.of_hasPushout i j)
      ((left_localized_isIso_iff f).mpr hf)
  have h₂ : IsIso (AnodyneHomotopy.anodyneQ.map t) :=
    MonoRightPushoutEquivalence.localized_isIso p (right_all_mono_rlp f) u₁ u t hs
  have he : AnodyneHomotopy.anodyneQ.map g₁ ≫ AnodyneHomotopy.anodyneQ.map t =
      AnodyneHomotopy.anodyneQ.map g :=
    (AnodyneHomotopy.anodyneQ.map_comp _ _).symm.trans
      (congrArg AnodyneHomotopy.anodyneQ.map hg)
  exact he ▸ inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map g₁ ≫
    AnodyneHomotopy.anodyneQ.map t))

include hf sq in
lemma image_isIso {D : Type uD} [Category.{vD} D] (L : SSet.{v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map g) :=
  AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL g (localized_isIso f hf j u g sq)

end SerrePositivity.SimplicialModel.KanLocalizedLeftProper
