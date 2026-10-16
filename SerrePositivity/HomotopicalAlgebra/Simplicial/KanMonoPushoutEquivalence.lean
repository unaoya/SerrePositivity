module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoRelativeHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoPushoutExtension

/-! # Pushouts preserve localized mono equivalences without a value model structure

Both endpoints and the entire homotopy on the pushout leg are retained
when gluing intervals. Kan class injectivity and surjectivity then detect
the localized equivalence of the actual pushout morphism.
-/

@[expose] public section
universe v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.KanMonoPushoutEquivalence
variable {A B C P K : SSet.{v}} (i : A ⟶ B) [Mono i]
  (j : A ⟶ C) (u : B ⟶ P) (g : C ⟶ P) (sq : IsPushout i j u g)
  (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include sq hi hK in
lemma exists_homotopy (f f' : P ⟶ K) (H : SSet.Homotopy (g ≫ f) (g ≫ f')) :
    ∃ V : SSet.Homotopy f f',
      g ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = H.h := by
  let HA := LargeParameterSquare.changeEndpoints (HomotopyClasses.preHomotopy j H)
    (by rw [← Category.assoc, ← sq.w, Category.assoc])
    (by rw [← Category.assoc, ← sq.w, Category.assoc])
  obtain ⟨HB, hB⟩ := KanMonoRelativeHomotopy.exists_extension i hi hK (u ≫ f) (u ≫ f') HA
  have hc : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ HB.h =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h := by
    rw [hB]
    dsimp only [HA]
    rw [LargeParameterSquare.changeEndpoints_h]
    rfl
  let tsq := sq.map (tensorRight (SSet.stdSimplex.obj (SimplexCategory.mk 1)))
  let q := tsq.desc HB.h H.h hc
  have hu : u ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ q = HB.h :=
    tsq.inl_desc _ _ _
  have hg : g ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ q = H.h :=
    tsq.inr_desc _ _ _
  refine ⟨{ h := q, h₀ := ?_, h₁ := ?_, rel := ?_ }, hg⟩
  · change SSet.ι₀ ≫ q = f
    apply sq.hom_ext
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hu, HB.h₀]
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hg, H.h₀]
  · change SSet.ι₁ ≫ q = f'
    apply sq.hom_ext
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hu, HB.h₁]
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hg, H.h₁]
  · apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

include sq hi hK in
lemma pre_injective : Function.Injective (HomotopyClasses.pre g (K := K)) := by
  intro x y h
  obtain ⟨f, rfl⟩ := Quot.exists_rep x
  obtain ⟨f', rfl⟩ := Quot.exists_rep y
  obtain ⟨H⟩ := KanActualHomotopy.of_class_eq hK h
  obtain ⟨V, _⟩ := exists_homotopy i j u g sq hi hK f f' H
  exact HomotopyClasses.sound V

include sq hi in
lemma tests : KanTestDetection.Tests g := by
  intro K hK
  exact ⟨pre_injective i j u g sq hi hK,
    KanMonoPushoutExtension.pre_surjective i j u g sq hi hK⟩

include sq hi in
lemma localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map g) :=
  (KanTestDetection.anodyneQ_isIso_iff_tests g).mpr (tests i j u g sq hi)

include sq hi in
lemma image_isIso {D : Type uH} [Category.{vH} D] (L : SSet.{v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map g) :=
  AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL g (localized_isIso i j u g sq hi)

end SerrePositivity.SimplicialModel.KanMonoPushoutEquivalence
