module

public import SerrePositivity.KST.Spectra.PointedHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso

/-!
# 指定点付き同型の全次数のホモトピー同値

DAG XIII §2.2 の cone 比較で使う一般の補助。元の点付き射の誘導写像を保持する。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets

/-- 元の点付き同型の誘導写像そのものを、全次数の集合の同値へ束ねる。 -/
def pointedIsoHomotopyEquiv {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (e : X ≅ Y) (n : ℕ) :
    KanHomotopy X.right n X.basepoint ≃ KanHomotopy Y.right n Y.basepoint :=
  KanHomotopy.equivOfIso n (show X.right ≅ Y.right from PointedSimplicialSet.forget.mapIso e)
    (pointedMap_basepoint e.hom)

@[simp]
lemma pointedIsoHomotopyEquiv_apply {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (e : X ≅ Y) (n : ℕ)
    (a : KanHomotopy X.right n X.basepoint) :
    pointedIsoHomotopyEquiv e n a =
      SerrePositivity.KST.Spectra.pointedHomotopyMap n e.hom a := rfl

end SerrePositivity.EInfinity.PowerOperation
