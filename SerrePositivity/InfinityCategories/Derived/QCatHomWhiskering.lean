module
public import SerrePositivity.InfinityCategories.Derived.SimplicialEnrichedComposition
public import SerrePositivity.InfinityCategories.F1B.QCatEquivalenceAdjunction
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedWhiskerAlgebra
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorCompositionWhiskerEdges
/-!
概要：quasicategory 双圏の whiskering を h Fun の前後合成へ同定する。
方針：実辺と全次数の成分を使って同じ作用を照合する。
規約：元の指定関手と射を保持する。使われ方：一般 cell 合成の単位 coherence。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private lemma arrowHom_heq_of_eq {C : Type*} [Category C] {a b c d : C}
    {f : a ⟶ b} {g : c ⟶ d} (h : Arrow.mk f = Arrow.mk g) : HEq f g := by
  have hh : HEq f (Arrow.mk f).hom := HEq.rfl
  rw [h] at hh
  exact hh

lemma qcatHomFunctor_map_whiskerLeft {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (p : X ⟶ Y) {f g : Y ⟶ Z} (a : qcatMap f ⟶ qcatMap g) :
    (qcatHomFunctor X Z).map (Bicategory.whiskerLeft (qcatMap p) a) =
      functorHomPrecomp f g p ((qcatHomFunctor Y Z).map a) := by
  change CatEnrichedOrdinary.Hom.base
    (CatEnrichedOrdinary.hComp (𝟙 (qcatMap p)) a) = _
  simp only [CatEnrichedOrdinary.hComp, CatEnrichedOrdinary.base_mk,
    ← heq_eq_eq, eqToHom_comp_heq_iff,
    comp_eqToHom_heq_iff]
  change HEq (CatEnriched.hComp (C := SSet.QCat)
    (a := qcatOf X) (b := qcatOf Y) (c := qcatOf Z) (𝟙 (HomotopyCategory.mk (functorVertex p)))
    ((qcatHomFunctor Y Z).map a)) _
  obtain ⟨ee, he⟩ := homotopyCategory_homMk_surjective (functorVertex f) (functorVertex g)
    ((qcatHomFunctor Y Z).map a)
  rw [← he]
  change HEq (((Functor.LaxMonoidal.μ hoFunctor ((ihom X).obj Y) ((ihom Y).obj Z)) ≫
    hoFunctor.map (eComp SSet X Y Z)).toFunctor.map
      (X := (HomotopyCategory.mk (functorVertex p), HomotopyCategory.mk (functorVertex f)))
      (Y := (HomotopyCategory.mk (functorVertex p), HomotopyCategory.mk (functorVertex g)))
      (𝟙 (HomotopyCategory.mk (functorVertex p)), Truncated.HomotopyCategory.homMk ee)) _
  rw [simplicialEnrichedComp_eq_internalComp]
  simp only [Cat.Hom.comp_toFunctor, CategoryTheory.Functor.comp_map]
  change HEq (Truncated.HomotopyCategory.homMk
    (((Truncated.Edge.id (X := (truncation 2).obj ((ihom X).obj Y))
      (functorVertex p)).tensor ee).map ((truncation 2).map (MonoidalClosed.comp X Y Z))))
    (Truncated.HomotopyCategory.homMk (ee.map ((truncation 2).map ((pre p).app Z))))
  have h := Truncated.HomotopyCategory.congr_arrowMk_homMk _ _
    (F2.functorComposition_pre_edge ee p)
  exact arrowHom_heq_of_eq h
lemma qcatHomFunctor_map_whiskerRight {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    {f g : X ⟶ Y} (a : qcatMap f ⟶ qcatMap g) (p : Y ⟶ Z) :
    (qcatHomFunctor X Z).map (Bicategory.whiskerRight a (qcatMap p)) =
      functorHomPostcomp f g p ((qcatHomFunctor X Y).map a) := by
  change CatEnrichedOrdinary.Hom.base
    (CatEnrichedOrdinary.hComp a (𝟙 (qcatMap p))) = _
  simp only [CatEnrichedOrdinary.hComp, CatEnrichedOrdinary.base_mk,
    ← heq_eq_eq, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  change HEq (CatEnriched.hComp (C := SSet.QCat)
    (a := qcatOf X) (b := qcatOf Y) (c := qcatOf Z)
    ((qcatHomFunctor X Y).map a) (𝟙 (HomotopyCategory.mk (functorVertex p)))) _
  obtain ⟨ee, he⟩ := homotopyCategory_homMk_surjective (functorVertex f) (functorVertex g)
    ((qcatHomFunctor X Y).map a)
  rw [← he]
  change HEq (((Functor.LaxMonoidal.μ hoFunctor ((ihom X).obj Y) ((ihom Y).obj Z)) ≫
    hoFunctor.map (eComp SSet X Y Z)).toFunctor.map
      (X := (HomotopyCategory.mk (functorVertex f), HomotopyCategory.mk (functorVertex p)))
      (Y := (HomotopyCategory.mk (functorVertex g), HomotopyCategory.mk (functorVertex p)))
      (Truncated.HomotopyCategory.homMk ee, 𝟙 (HomotopyCategory.mk (functorVertex p)))) _
  rw [simplicialEnrichedComp_eq_internalComp]
  simp only [Cat.Hom.comp_toFunctor, CategoryTheory.Functor.comp_map]
  change HEq (Truncated.HomotopyCategory.homMk
    ((ee.tensor (Truncated.Edge.id (X := (truncation 2).obj ((ihom Y).obj Z))
      (functorVertex p))).map ((truncation 2).map (MonoidalClosed.comp X Y Z))))
    (Truncated.HomotopyCategory.homMk (ee.map ((truncation 2).map ((ihom X).map p))))
  have h := Truncated.HomotopyCategory.congr_arrowMk_homMk _ _
    (F2.functorComposition_post_edge ee p)
  exact arrowHom_heq_of_eq h

end
end SerrePositivity.InfinityCategories
