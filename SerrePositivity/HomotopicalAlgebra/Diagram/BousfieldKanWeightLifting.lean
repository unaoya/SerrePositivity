module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanCoefficientFibration

/-!
概要：BK endの既存の自明fibration保存を、BK重みからの自然変換の持ち上げへ移す。
方針：単位パラメータで切断空間へ転置し、空対象からの持ち上げを元に戻す。
規約：値のKan性や遷移のfibration性を仮定しない。指定された右辺の射を回収する。
使われ方：HTT 4.2.4.4のRR02(a)、実際のBK重みの射影的cofibrancyへの入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.DiagramModel
variable {K : Type u} [SmallCategory K]

/-- BK重みからの実自然変換は、係数ごとの自明Kan fibrationに沿って持ち上がる。 -/
lemma exists_bousfieldKanWeight_lift {F G : K ⥤ SSet.{u}} (p : F ⟶ G)
    [∀ k, TrivialKanFibration (p.app k)] (a : bousfieldKanWeight K ⟶ G) :
    ∃ b : bousfieldKanWeight K ⟶ F, b ≫ p = a := by
  let W := bousfieldKanWeight K
  let q := weightedSectionsMap W p
  have hq : TrivialKanFibration q := bousfieldKanMap_trivialKanFibration p
  let v : (𝟙_ SSet.{u}) ⟶ weightedSections W G :=
    weightedSectionsLift ((ρ_ W).hom ≫ a)
  have : HasLiftingProperty (initial.to (𝟙_ SSet.{u})) q :=
    hq.mem _ inferInstance
  let sq : CommSq (initial.to (weightedSections W F))
      (initial.to (𝟙_ SSet.{u})) q v := ⟨initial.hom_ext _ _⟩
  refine ⟨(ρ_ W).inv ≫ weightedSectionsUncurry sq.lift, ?_⟩
  rw [Category.assoc, ← weightedSectionsUncurry_postcomp, sq.fac_right]
  change (ρ_ W).inv ≫ weightedSectionsUncurry
    (weightedSectionsLift ((ρ_ W).hom ≫ a)) = a
  rw [weightedSectionsUncurry_lift, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.DiagramModel
