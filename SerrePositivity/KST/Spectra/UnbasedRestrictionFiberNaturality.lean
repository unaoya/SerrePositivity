module

public import SerrePositivity.KST.Spectra.PointedCofiberMappingNaturality
public import SerrePositivity.KST.Spectra.UnbasedMappingFiberIso
public import SerrePositivity.KST.Spectra.UnbasedMappingPost

/-!
概要：通常の写像空間の制限の fiber の cofiber 表示の係数自然性。
方針：fiber 包含後の商射による制限と自由基点の Hom の比較を照合する。
規約：源の射の単射性も係数の Kan 性も要求しない。
使われ方：Goerss–Jardine VIII §1。骨格の相対商の模型の自然性。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[reassoc]
lemma freeHomIso_post (K : SSet.{u}) {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    PointedObject.basedHomMap (PointedObject.adjoin K) (Y := Y) (Z := Z) p ≫
        (freeHomIso K Z).hom = (freeHomIso K Y).hom ≫ post K p := by
  apply Under.UnderMorphism.ext
  exact FreePointedHomRestriction.natural_post K p

/-- 概要：通常の制限射の fiber が係数の後合成で移る射。
方針：制限と後合成の可換正方形を pointwise fiber へ送る。
規約：Kan 性は不要。
使われ方：Goerss–Jardine VIII §1。骨格の fiber の係数射の一般形。 -/
def restrictionFiberMap {K L : SSet.{u}} (f : K ⟶ L)
    {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    pointedFiber (pre f Y) ⟶ pointedFiber (pre f Z) :=
  PointedFiberComparison.map _ _ (post L p) (post K p) (pre_post f p)

@[reassoc]
lemma restrictionFiberIso_hom_ι {K L : SSet.{u}} (f : K ⟶ L)
    (X : PointedSimplicialSet.{u}) :
    (restrictionFiberIso f X).hom ≫ pointedFiberι (pre f X) =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection (PointedObject.adjoinFunctor.map f)) X ≫
        (freeHomIso L X).hom := by
  dsimp only [restrictionFiberIso, Iso.trans_hom, PointedFiberComparison.iso]
  rw [Category.assoc, PointedFiberComparison.map_ι]
  rw [← Category.assoc, pointedCofiberMappingFiberIso_hom_ι]

/-- 概要：相対 cofiber の Hom による制限の fiber の表示は係数射に自然。
方針：fiber の包含後で商射への前合成と自由基点の Hom の自然性を使う。
規約：同型の実際の射に対する厳密な可換式。
使われ方：Goerss–Jardine VIII §1。骨格のセルの係数の自然な同定。 -/
@[reassoc]
lemma restrictionFiberIso_natural {K L : SSet.{u}} (f : K ⟶ L)
    {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    PointedObject.basedHomMap (relativeSource f) (Y := Y) (Z := Z) p ≫
        (restrictionFiberIso f Z).hom =
      (restrictionFiberIso f Y).hom ≫ restrictionFiberMap f p := by
  apply pointedFiber_hom_ext (pre f Z)
  dsimp only [relativeSource]
  have hi : restrictionFiberMap f p ≫ pointedFiberι (pre f Z) =
      pointedFiberι (pre f Y) ≫ post L p :=
    PointedFiberComparison.map_ι (pre f Y) (pre f Z) (post L p) (post K p) (pre_post f p)
  rw [Category.assoc, restrictionFiberIso_hom_ι]
  erw [Category.assoc, hi, restrictionFiberIso_hom_ι_assoc]
  rw [← freeHomIso_post, ← Category.assoc]
  rw [← PointedMapping.prePointed_post]
  simp only [Category.assoc]
  rfl

end

end SerrePositivity.KST.Spectra.UnbasedPointedMapping
