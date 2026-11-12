module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SimplicialHomEnriched
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallKanHomContinuity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanSourceReplacement

/-!
概要：任意の始点射による全 Hom の前合成を豊穣比較とし、anodyne な Kan 置換では全自然同型にする。
方針：全パラメーターの前合成と後合成を照合し、既存の実 Hom ホモトピー同値を同じ比較へ適用する。
規約：値ごとの逆同値を選ばない。元の始点射と全高次射の作用を保持する。
使われ方：有限模型の Kan 置換の compact 性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 始点の射による前合成は、全高次射に関して自然な豊穣比較。 -/
def simplicialHomSourceComparison {A B : SSet.{u}} (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomEnriched B) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomEnriched A) := by
  refine ⟨fun X ↦ (pre f).app X.obj, ?_⟩
  intro X Y
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨g, h⟩
  apply Functor.HomObj.ext
  funext m α
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- anodyne な始点射による同じ全前合成比較は、coherent nerve 上で全自然同型。 -/
def simplicialHomSourceComparisonIso {A B : SSet.{u}} (f : A ⟶ B)
    (hf : SSet.anodyneExtensions f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomInfinity B) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomInfinity A) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonIso (simplicialHomSourceComparison f)
    (fun X ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.homotopyEquivalence_pre_of_anodyne f hf X.obj).isQCatEquivalence)

/-- 元の連続 Kan 置換を、そのまま Kan 対象に束縛する。 -/
def continuousReplacementKanObject (A : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj A, inferInstance⟩

/-- 元の Kan 置換からの全 Hom と、元の始点からの全 Hom の全自然同型。 -/
def continuousReplacementHomIso (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanInternalHomInfinity (continuousReplacementKanObject A))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomInfinity A) :=
  simplicialHomSourceComparisonIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit_anodyne A)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
