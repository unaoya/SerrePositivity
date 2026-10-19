module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedSectionsParameters

/-!
概要：共有の weighted end の全パラメータ作用と係数の自然変換の両立。
方針：各射影を評価し、係数の可換な四角形と結合子の自然性を使う。
規約：係数の同型性・Kan 性・添字の形状は不要。使われ方：元の Hom 図式への同型の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra.WeightedParameterNaturality
variable {I : Type u} [SmallCategory I]

/-- 係数の射による end の写像は、各射影で元の係数の射になる。 -/
@[reassoc]
lemma map_evaluation (W : I ⥤ SSet.{u}) {H H' : I ⥤ SSet.{u}} (α : H ⟶ H') (i : I) :
    W.obj i ◁ weightedSectionsMap W α ≫ uncurry (weightedSectionsπ W H' i) =
      uncurry (weightedSectionsπ W H i) ≫ α.app i := by
  rw [← uncurry_natural_left, weightedSectionsMap_π, uncurry_natural_right]

/-- パラメータ付き係数の可換な四角形は、weighted end 上でも可換。 -/
lemma natural (W : I ⥤ SSet.{u}) {H H' E E' : I ⥤ SSet.{u}} {B : SSet.{u}}
    (α : H ⟶ H') (β : E ⟶ E') (η : H ⋙ tensorRight B ⟶ E)
    (θ : H' ⋙ tensorRight B ⟶ E')
    (h : ∀ i, α.app i ▷ B ≫ θ.app i = η.app i ≫ β.app i) :
    weightedSectionsMap W α ▷ B ≫ weightedSectionsParameterMap W θ =
      weightedSectionsParameterMap W η ≫ weightedSectionsMap W β := by
  apply weightedSections_hom_ext
  intro i
  apply uncurry_injective
  conv_lhs =>
    rw [Category.assoc, uncurry_natural_left, uncurry_natural_left,
      weightedSectionsParameterMap_evaluation, associator_inv_naturality_middle_assoc,
      ← comp_whiskerRight_assoc, map_evaluation, comp_whiskerRight_assoc, h]
  conv_rhs =>
    rw [Category.assoc, weightedSectionsMap_π, ← Category.assoc, uncurry_natural_right,
      uncurry_natural_left, weightedSectionsParameterMap_evaluation]
  simp only [Category.assoc]

end SerrePositivity.KST.Spectra.WeightedParameterNaturality
