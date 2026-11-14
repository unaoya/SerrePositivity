module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanTensorLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
概要：BK endは係数ごとのKan fibrationを保つ。
方針：braidingでtensorの順を合わせ、既存の切断随伴で持ち上げを移す。
使われ方：HTT 4.2.4.4、RR02(a)の実現随伴のhorn条件。
規約：係数の遷移のfibration性も、SSetモデル構造も要求しない。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open SerrePositivity.PointwiseAdjunction
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel
variable (K : Type u) [SmallCategory K]

/-- 左のパラメータを右へ移す、成分ごとのbraiding。 -/
def bousfieldKanParameterSwap (A : SSet.{u}) :
    ((pointwise K (curriedTensor SSet.{u})).obj A).obj (bousfieldKanWeight K) ≅
      (weightedParameterFunctor (bousfieldKanWeight K)).obj A :=
  NatIso.ofComponents (fun k => β_ A ((bousfieldKanWeight K).obj k)) (by
    intro k l f
    exact BraidedCategory.braiding_naturality_right A ((bousfieldKanWeight K).map f))

/-- 同じtensor射をbraidingで移した持ち上げ条件。 -/
lemma bousfieldKanParameter_hasLiftingProperty {A B : SSet.{u}}
    (i : A ⟶ B) (hi : SSet.anodyneExtensions i)
    {F G : K ⥤ SSet.{u}} (p : F ⟶ G) [∀ k, Fibration (p.app k)] :
    HasLiftingProperty ((weightedParameterFunctor (bousfieldKanWeight K)).map i) p := by
  let e : Arrow.mk (((pointwise K (curriedTensor SSet.{u})).map i).app
      (bousfieldKanWeight K)) ≅
      Arrow.mk ((weightedParameterFunctor (bousfieldKanWeight K)).map i) :=
    Arrow.isoMk (bousfieldKanParameterSwap K A) (bousfieldKanParameterSwap K B) (by
      apply NatTrans.ext
      funext k
      exact BraidedCategory.braiding_naturality_left i ((bousfieldKanWeight K).obj k))
  exact (HasLiftingProperty.iff_of_arrow_iso_left e p).mp
    (bousfieldKanTensor_hasLiftingProperty K i hi p)

/-- 既存の切断随伴による、係数Kan fibrationの保存。 -/
lemma bousfieldKanEndMap_fibration
    {F G : K ⥤ SSet.{u}} (p : F ⟶ G) [∀ k, Fibration (p.app k)] :
    Fibration (weightedSectionsMap (bousfieldKanWeight K) p) := by
  apply InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_hasLiftingProperty_horn
  intro n i
  exact ((weightedSectionsAdjunction (bousfieldKanWeight K)).hasLiftingProperty_iff
    (SSet.horn (n + 1) i).ι p).mp
    (bousfieldKanParameter_hasLiftingProperty K _ (SSet.anodyneExtensions.horn_ι i) p)

end SerrePositivity.DiagramModel
