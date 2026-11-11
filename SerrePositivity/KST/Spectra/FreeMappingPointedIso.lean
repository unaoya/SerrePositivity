module

public import SerrePositivity.KST.Spectra.PointedSkeletalMappingTower
public import SerrePositivity.KST.Spectra.PointedWeightedEndBasepoint

/-!
概要：自由基点を加えた源からの点つき Hom と定数基点の写像空間の同型。
方針：元の成分への制限の同型が基点を保つ式を使う。
規約：源の射での前合成に自然な点つき同型。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の塔の fiber の cofiber 表示。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：自由基点を加えた源からの点つき Hom は定数基点の写像空間。
方針：元の成分への制限と基点の定数族の式を束ねる。
規約：係数の Kan 性は不要。
使われ方：Goerss–Jardine I §7、VIII §1。通常の写像空間の点つき閉構造による表示。 -/
def freeHomIso (K : SSet.{u}) (X : PointedSimplicialSet.{u}) :
    PointedObject.basedHom (PointedObject.adjoin K) X ≅ obj K X :=
  Under.isoMk (FreePointedHomRestriction.iso K X)
    (FreePointedHomRestriction.basepoint_restrict K X)

@[reassoc]
lemma freeHomIso_pre {K L : SSet.{u}} (f : K ⟶ L) (X : PointedSimplicialSet.{u}) :
    (MonoidalClosed.pre (PointedObject.adjoinFunctor.map f)).app X ≫ (freeHomIso K X).hom =
      (freeHomIso L X).hom ≫ pre f X := by
  apply Under.UnderMorphism.ext
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  exact FreePointedHomRestriction.natural_pre f X

end

end SerrePositivity.KST.Spectra.UnbasedPointedMapping
