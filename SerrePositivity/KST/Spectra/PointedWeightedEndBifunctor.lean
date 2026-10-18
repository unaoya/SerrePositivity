module

public import SerrePositivity.KST.Spectra.PointedWeightedEndPreMap

/-!
概要：点つき end の重みの前合成と係数の後合成の可換性。
方針：各 end 射影で内部 Hom の二つの変数の自然性を使う。
規約：全ての等式は通常の点つき射の厳密な等式。
使われ方：Goerss–Jardine VIII §§1–2、HA §1.4.2。余単体 cochain 図式の係数の自然性。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet
open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.PointedWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance weightedEndBifunctorSelfEnrichment : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
  enrichedOrdinaryCategorySelf SSet.{u}

local instance weightedEndBifunctorPointedSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- 概要：重みの前合成と係数の後合成は可換。
方針：end の各射影で内部 Hom の二変数の交換則を使う。
規約：添字圏と図式に Kan 条件は不要。
使われ方：Goerss–Jardine VIII §2。余単体 cochain への係数の射の自然性。 -/
lemma map_preMap {I : Type u} [SmallCategory I] {W V : I ⥤ SSet.{u}} (θ : W ⟶ V)
    {D E : I ⥤ PointedSimplicialSet.{u}} (τ : D ⟶ E) :
    map V τ ≫ preMap θ E = preMap θ D ≫ map W τ := by
  apply end_.hom_ext
  intro i
  rw [Category.assoc, preMap_π, ← Category.assoc, map_π]
  conv_rhs => rw [Category.assoc, map_π, ← Category.assoc, preMap_π]
  rw [Category.assoc, Category.assoc]
  apply congrArg (fun t ↦ end_.π (diagram V D) i ≫ t)
  exact (pre_comm_ihom_map (PointedObject.adjoinFunctor.map (θ.app i)) (τ.app i)).symm

end

end SerrePositivity.KST.Spectra.PointedWeightedEnd
