module

public import SerrePositivity.KST.Spectra.PointedWeightedEndPreMap
public import SerrePositivity.KST.Spectra.PointedWeightedCone

/-!
概要：厳密な錐から点つき end への標準射の重みの前合成への自然性。
方針：end の各射影で、定数族を前合成しても変わらないことを使う。
規約：錐の極限性や図式の Kan 性は不要。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。自明作用の cochain の標準拡大。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet
open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.PointedWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance weightedConePreMapPointedSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- 概要：錐の定数族を重みの射で前合成すると元の重みでの定数族になる。
方針：end の各射影の式と定数族の前合成の不変性を使う。
規約：標準比較は極限錐でなくても定義される。
使われ方：Goerss–Jardine VIII §2。自明作用の cochain の余単体標準射。 -/
lemma coneComparison_preMap {I : Type u} [SmallCategory I] {W V : I ⥤ SSet.{u}}
    (θ : W ⟶ V) {D : I ⥤ PointedSimplicialSet.{u}} (c : Cone D) :
    coneComparison V c ≫ preMap θ D = coneComparison W c := by
  apply end_.hom_ext
  intro i
  rw [Category.assoc, preMap_π, ← Category.assoc, coneComparison_π, coneComparison_π,
    Category.assoc, constantFamily_pre]

end

end SerrePositivity.KST.Spectra.PointedWeightedEnd
