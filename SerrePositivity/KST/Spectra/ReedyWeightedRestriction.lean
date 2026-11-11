module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedCorner
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor
public import SerrePositivity.KST.Spectra.CosimplicialHornFactorization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Lifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.MonoRightHomotopyEquivalence

/-!
概要：重み付き end の制限の充填を相対 tensor の Reedy 持ち上げに帰着する。
方針：二つの転置した族を pushout-product 上で貼り、Reedy filler を再び curry する。
規約：対象ごとの Kan 性だけで end の制限の弱同値性を仮定しない。
使われ方：Goerss–Jardine VII §4、VIII §1。通常 Tot と BK Tot の比較の相対持ち上げ。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.ReedyWeightedRestriction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I]

/-- 相対 tensor から終射への持ち上げを end の制限の持ち上げへ転置する。 -/
lemma hasLiftingProperty {W V H : I ⥤ SSet.{u}} (θ : W ⟶ V)
    {A B : SSet.{u}} (i : A ⟶ B)
    [HasLiftingProperty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner θ i).ι (terminal.from H)] :
    HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre θ H) := by
  constructor
  intro t s sq
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner θ i
  have hw : (θ ▷ (Functor.const I).obj A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry t =
      (W ◁ (Functor.const I).map i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry s := by
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry sq.w
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_comp_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_precomp] at h
    exact h
  let a := P.isPushout.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry s) hw
  let q : CommSq a P.ι (terminal.from H) (terminal.from _) :=
    ⟨terminal.hom_ext _ _⟩
  refine CommSq.HasLift.mk' { l := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift q.lift, fac_left := ?_, fac_right := ?_ }
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv V H A).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift q.lift) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
    calc
      _ = (P.inl ≫ P.ι) ≫ q.lift := congrArg (fun f ↦ f ≫ q.lift) P.inl_ι.symm
      _ = _ := by rw [Category.assoc, q.fac_left]; exact P.isPushout.inl_desc _ _ _
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv W H B).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift q.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre θ H) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_comp_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
    calc
      _ = (P.inr ≫ P.ι) ≫ q.lift := congrArg (fun f ↦ f ≫ q.lift) P.inr_ι.symm
      _ = _ := by rw [Category.assoc, q.fac_left]; exact P.isPushout.inr_desc _ _ _

variable {inverse direct : MorphismProperty I}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ)

/-- 相対 tensor が Reedy anodyne なら Reedy fibrant な係数で実際に充填できる。 -/
lemma hasLiftingProperty_of_reedy {W V H : I ⥤ SSet.{u}} (θ : W ⟶ V)
    {A B : SSet.{u}} (i : A ⟶ B)
    (hθ : reedyLeft r anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner θ i).ι)
    (hH : reedyRight r J.rlp (terminal.from H)) :
    HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre θ H) := by
  let := CosimplicialHornFactorization.hornWeakFactorization.{u}
  let : ∀ j, HasLiftingProperty (relativeLatchingMap r j (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner θ i).ι)
      (relativeMatchingMap r j (terminal.from H)) := fun j ↦
    MorphismProperty.hasLiftingProperty_of_wfs _ _ (hθ j) (hH j)
  let : HasLiftingProperty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner θ i).ι (terminal.from H) :=
    Lifting.hasLiftingProperty r
  exact hasLiftingProperty θ i

/-- 全ての相対境界 tensor の Reedy anodyne 性は end の制限の全境界充填を与える。 -/
lemma trivialKanFibration_of_reedy {W V H : I ⥤ SSet.{u}} (θ : W ⟶ V)
    (hθ : ∀ n : ℕ, reedyLeft r anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner θ (boundary n).ι).ι)
    (hH : reedyRight r J.rlp (terminal.from H)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre θ H) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  exact hasLiftingProperty_of_reedy r θ (boundary n).ι (hθ n) hH

/-- Reedy の相対境界充填は Kan な両 end の全基点 π 同型へ移る。 -/
lemma piIsomorphism_of_reedy {W V H : I ⥤ SSet.{u}} (θ : W ⟶ V)
    [KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H)] [KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections V H)]
    (hθ : ∀ n : ℕ, reedyLeft r anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCorner θ (boundary n).ι).ι)
    (hH : reedyRight r J.rlp (terminal.from H)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre θ H) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (trivialKanFibration_of_reedy r θ hθ hH).mem

end
end SerrePositivity.KST.Spectra.ReedyWeightedRestriction
