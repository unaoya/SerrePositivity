module

public import SerrePositivity.InfinityCategories.F2.Presentable.SimplicialHomEnriched
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallKanHomContinuity
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ContinuousKanAnodyne
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanSourceReplacement

/-!
概要：任意の始点射による全 Hom の前合成を豊穣比較とし、anodyne な Kan 置換では全自然同型にする。
方針：全パラメーターの前合成と後合成を照合し、既存の実 Hom ホモトピー同値を同じ比較へ適用する。
規約：値ごとの逆同値を選ばない。元の始点射と全高次射の作用を保持する。
使われ方：有限模型の Kan 置換の compact 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 始点の射による前合成は、全高次射に関して自然な豊穣比較。 -/
def simplicialHomSourceComparison {A B : SSet.{u}} (f : A ⟶ B) :
    KanEnrichedComparison (simplicialInternalHomEnriched B) (simplicialInternalHomEnriched A) := by
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
    FunctorIso (simplicialInternalHomInfinity B) (simplicialInternalHomInfinity A) :=
  kanEnrichedComparisonIso (simplicialHomSourceComparison f)
    (fun X ↦ (HomotopyLimits.homotopyEquivalence_pre_of_anodyne f hf X.obj).isQCatEquivalence)

/-- 元の連続 Kan 置換を、そのまま Kan 対象に束縛する。 -/
def continuousReplacementKanObject (A : SSet.{u}) : KanObject.{u} :=
  ⟨continuousKanReplacement.obj A, inferInstance⟩

/-- 元の Kan 置換からの全 Hom と、元の始点からの全 Hom の全自然同型。 -/
def continuousReplacementHomIso (A : SSet.{u}) :
    FunctorIso (kanInternalHomInfinity (continuousReplacementKanObject A))
      (simplicialInternalHomInfinity A) :=
  simplicialHomSourceComparisonIso (continuousKanReplacementUnit.app A)
    (continuousKanReplacementUnit_anodyne A)

end SerrePositivity.InfinityCategories.F2.Presentable
