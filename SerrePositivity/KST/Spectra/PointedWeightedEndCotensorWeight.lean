module

public import SerrePositivity.KST.Spectra.PointedWeightedEndPreMap
public import SerrePositivity.KST.Spectra.PointedWeightedConeCompatibility

/-!
概要：点つき end と内部 Hom の交換同型の重みへの自然性。
方針：各 end 射影で二重内部 Hom の第二の源への自然性を使う。
規約：係数への自然性と合わせて cochain の余単体構造を保持する。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain と loop の交換。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet
open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.PointedWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance weightedEndCotensorWeightPointedSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- 概要：内部 Hom と end の交換は重みの自然変換の前合成と可換。
方針：各射影の式と二重内部 Hom の第二の源の制限の可換式を使う。
規約：A は円に限らず任意の点つき単体集合。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain の loop 交換の余単体自然性。 -/
lemma cotensorIso_preMap (A : PointedSimplicialSet.{u})
    {I : Type u} [SmallCategory I] {W V : I ⥤ SSet.{u}} (θ : W ⟶ V)
    (D : I ⥤ PointedSimplicialSet.{u}) :
    (ihom A).map (preMap θ D) ≫ (cotensorIso A W D).hom =
      (cotensorIso A V D).hom ≫ preMap θ (D ⋙ ihom A) := by
  apply end_.hom_ext
  intro i
  change ((ihom A).map (preMap θ D) ≫ (cotensorIso A W D).hom) ≫
      end_.π (diagram W (D ⋙ ihom A)) i =
    ((cotensorIso A V D).hom ≫ preMap θ (D ⋙ ihom A)) ≫
      end_.π (diagram W (D ⋙ ihom A)) i
  conv_lhs =>
    rw [Category.assoc, cotensorIso_π, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      preMap_π, CategoryTheory.Functor.map_comp, Category.assoc]
  conv_rhs =>
    rw [Category.assoc, preMap_π, ← Category.assoc, cotensorIso_π, Category.assoc]
  apply congrArg (fun t ↦ (ihom A).map (end_.π (diagram V D) i) ≫ t)
  exact _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right A (PointedObject.adjoinFunctor.map (θ.app i))
    (D.obj i)

end

end SerrePositivity.KST.Spectra.PointedWeightedEnd
