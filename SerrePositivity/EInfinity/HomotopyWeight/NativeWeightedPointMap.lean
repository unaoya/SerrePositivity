module
public import SerrePositivity.EInfinity.HomotopyWeight.NativeWeightedPointRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor

/-!
概要：元の指定重み付き錐の点を、同じ係数図式の射の後合成で追跡する。
方針：既存の転置の後合成則を標準零単体で評価する。
規約：IS-W2 R02〜R03の自然性の法則。元の自然変換の実際の後合成。
使われ方：右frameの係数同型による指定BK普遍点の輸送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

/-- 同じ係数図式の射は、元の指定錐の同じ点を後合成へ送る。 -/
theorem nativeWeightedPoint_map {W F G : I ⥤ SSet.{u}} (s : W ⟶ F) (f : F ⟶ G) :
    ((weightedSectionsMap W f).app (Opposite.op ⦋0⦌)) (nativeWeightedPoint I s) =
      nativeWeightedPoint I (s ≫ f) := by
  rw [nativeWeightedPoint, nativeWeightedPoint, ← SSet.yonedaEquiv_comp,
    ← weightedSectionsLift_postcomp, Category.assoc]

end SerrePositivity.EInfinity.HomotopyWeight
