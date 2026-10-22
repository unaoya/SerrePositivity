module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafRightFiberPointedIso
public import SerrePositivity.InfinityCategories.F1.UniverseEquivalenceDescent

/-!
概要：元の right unstraightening の反転 fiber と元の前層の指定値を同じ宇宙で比較する。
方針：元の pointed fiber 同型と値の比較を続け、その同じ順方向の射を元の宇宙へ降ろす。
規約：持ち上げた順方向の射の厳密な回収式を保つ。
使われ方：元の始点固定の弱同値による密度の評価値写像の検査。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F
local notation "z" => presheafDensityEvaluationVertex F x
local instance : KanComplex (vertexFiber p x) := vertexFiber_kanComplex p x

/-- 元の反転 fiber の持ち上げから、元の評価頂点の値への同じ比較。 -/
def presheafRightFiberLiftedValueEquivalence :
    QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj (vertexFiber p x).op)
      ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z).obj) :=
  (qCatEquivalenceOfIso (presheafRightFiberPointedIso F x)).trans
    (pointedSpaceFiberValueEquivalence z)

/-- 元の反転 fiber と元の評価値は、元の宇宙で同値。 -/
def presheafRightFiberValueEquivalence :
    QCatEquivalence (vertexFiber p x).op (spaceInfinityObject z).obj :=
  (presheafRightFiberLiftedValueEquivalence F x).downOfKan

/-- 同じ小さい順方向の射を持ち上げると、元の pointed fiber を通る大きい比較を厳密に回収。 -/
lemma presheafRightFiberValueEquivalence_lift :
    (SSet.uliftFunctor.{u + 1, u}).map (presheafRightFiberValueEquivalence F x).hom =
      (presheafRightFiberPointedIso F x).hom ≫ (pointedSpaceFiberValueEquivalence z).hom := by
  change (SSet.uliftFunctor.{u + 1, u}).map
    (uliftMorphismDown (presheafRightFiberLiftedValueEquivalence F x).hom) = _
  exact uliftMorphismDown_lift _

end SerrePositivity.InfinityCategories.F2.Ind
