module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionsDiagramNaturality

/-!
概要：底を保つ写像の持ち上げ性を切断空間の誘導写像へ移す。
方針：切断の族を評価し、底とパラメータの直積上の相対持ち上げを解く。
規約：全空間の写像の fibration 性と、底の射影の fibration 性を区別する。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断模型の比較と選択空間の充填。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
variable {K E E' A B : SSet.{u}} {p : E ⟶ K} {q : E' ⟶ K}

/-- 概要：底とパラメータの直積の持ち上げ性は切断空間の持ち上げ性を与える。
方針：両方の切断の族を評価して持ち上げ、底の条件で切断空間へ戻す。
規約：パラメータの写像 i の単射性はこの一般の補題には不要。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断空間の相対充填。 -/
lemma simplicialSectionsMap_hasLiftingProperty (f : E ⟶ E') (hf : f ≫ q = p)
    (i : A ⟶ B) [HasLiftingProperty (K ◁ i) f] :
    HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf) := by
  constructor
  intro a b sq
  let t := (K ◁ a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p
  let u := (K ◁ b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation q
  have hs : CommSq t (K ◁ i) f u := by
    constructor
    dsimp only [t, u]
    rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap_evaluation f hf, ← Category.assoc,
      ← whiskerLeft_comp, sq.w, whiskerLeft_comp, Category.assoc]
  have hbase : hs.lift ≫ p = fst K B := by
    rw [← hf, ← Category.assoc, hs.fac_right]
    dsimp only [u]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation_projection, whiskerLeft_fst]
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift hs.lift hbase
  apply CommSq.HasLift.mk'
  refine { l := l, fac_left := ?_, fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
    rw [whiskerLeft_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift_evaluation]
    exact hs.fac_left
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
    rw [whiskerLeft_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap_evaluation,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift_evaluation]
    exact hs.fac_right

/-- 概要：全空間の底を保つ Kan fibration は切断空間の Kan fibration を誘導する。
方針：ホーンの底との直積が anodyne であることを用いて相対持ち上げを解く。
規約：底への二つの射影自身に fibration 性は要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断空間の相対的な比較。 -/
lemma simplicialSectionsMap_fibration (f : E ⟶ E') (hf : f ≫ q = p) [Fibration f] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_hasLiftingProperty_horn
  intro n i
  have : HasLiftingProperty (K ◁ (horn (n + 1) i).ι) f :=
    (anodyneExtensions.whiskerLeft (anodyneExtensions.horn_ι i) K) _
      ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)
  exact simplicialSectionsMap_hasLiftingProperty f hf _

/-- 概要：全空間の底を保つ trivial Kan fibration は切断空間の trivial Kan fibration を誘導する。
方針：境界と底の直積の単射性を使って全境界の持ち上げを解く。
規約：始域と終域の Kan 性は不要。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断模型の比較の可縮な選択空間。 -/
lemma simplicialSectionsMap_trivialKanFibration (f : E ⟶ E') (hf : f ≫ q = p)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap f hf) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  have : Mono (K ◁ (boundary n).ι) := by
    rw [NatTrans.mono_iff_mono_app]
    intro d
    rw [mono_iff_injective]
    intro x y h
    change (x.1, x.2.val) = (y.1, y.2.val) at h
    apply Prod.ext
    · exact (Prod.mk.inj h).1
    · apply Subtype.val_injective
      exact (Prod.mk.inj h).2
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := f) (K ◁ (boundary n).ι) inferInstance
  exact simplicialSectionsMap_hasLiftingProperty f hf _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
