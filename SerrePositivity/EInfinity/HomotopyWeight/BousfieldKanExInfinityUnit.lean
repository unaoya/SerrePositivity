module
public import SerrePositivity.EInfinity.HomotopyWeight.NativeWeightedPointMap
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityLocalization
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanHomotopyInvariance

/-!
概要：同じBK切断に、元の係数のEx∞単位を適用する。
方針：Kan係数上の単位の弱同値性と既存のBK係数不変性を使う。
規約：IS-W2 R02〜R03の既存の係数移送則。元の指定点の等式を保持する。
使われ方：同じBE TotのBK錐を全Hom∞比較の第零図式へ送る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable (I : Type u) [SmallCategory I]

/-- 元の全係数図式における、同じEx∞単位。 -/
def bousfieldKanExInfinityCoefficientUnit (H : I ⥤ SSet.{u}) : H ⟶ H ⋙ exInfinity :=
  Functor.whiskerLeft H exInfinityUnit

/-- Kan係数の同じ単位は、同じBK切断の実際のホモトピー同値を誘導する。 -/
theorem bousfieldKanExInfinityUnit_homotopyEquivalence (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] :
    IsSimplicialHomotopyEquivalence
      (weightedSectionsMap (bousfieldKanWeight I) (bousfieldKanExInfinityCoefficientUnit I H)) := by
  have (i : I) : KanComplex ((H ⋙ exInfinity).obj i) := by
    change KanComplex (exInfinity.obj (H.obj i))
    infer_instance
  apply bousfieldKanMap_homotopyEquivalence
  intro i
  apply IsWeakHomotopyEquivalence.isSimplicialHomotopyEquivalence
  exact FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence
    (exInfinityUnit.app (H.obj i)) (exInfinityUnit_localized_isIso (H.obj i))

/-- 同じ係数単位は、元の指定錐の零単体をその合成の零単体へ送る。 -/
theorem bousfieldKanExInfinityUnit_point {H : I ⥤ SSet.{u}}
    (s : bousfieldKanWeight I ⟶ H) :
    ((weightedSectionsMap (bousfieldKanWeight I)
      (bousfieldKanExInfinityCoefficientUnit I H)).app (Opposite.op ⦋0⦌))
        (nativeWeightedPoint I s) = nativeWeightedPoint I
          (s ≫ bousfieldKanExInfinityCoefficientUnit I H) :=
  nativeWeightedPoint_map I s _

end SerrePositivity.EInfinity.HomotopyWeight
