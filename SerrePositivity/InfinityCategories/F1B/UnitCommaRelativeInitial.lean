module

public import SerrePositivity.InfinityCategories.F1B.UniversalUnitComma
public import SerrePositivity.InfinityCategories.Stable.CartesianInitialBoundary

/-!
概要：comma の fiber の始対象性から、輸送を仮定して相対始点境界充填を得る。
方針：反転した始域射影の cocartesian 輸送を相対始対象の一般定理へ渡す。
規約：始域射影の輸送の構成を隠さず型クラス仮定として明示する。
使われ方：B1 の点ごとの単位比較から自然な余単位への残る橋を分離する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単位の fiber 内の始対象性は、始域射影の輸送があれば相対境界充填を与える。
方針：指定頂点の fiber の添字を揃え、反転した輸送の一般定理を使う。
規約：反転した始域射影の cocartesian fibration 性を明示的に仮定する。
使われ方：族への相対充填と自然な余単位候補の構成への入力。 -/
lemma UnitCommaInitialCondition.initialBoundaryLifting_of_op_transport
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : FunctorHom (𝟙 X) (F ≫ G)}
    [CocartesianHornFibration (SSet.opFunctor.map (unitCommaSource G))]
    (hη : UnitCommaInitialCondition η) (x : X _⦋0⦌) :
    InitialBoundaryLifting (unitCommaSource G)
      ((unitCommaSection η).app (Opposite.op ⦋0⦌) x) := by
  exact initialBoundaryLifting_of_isInitialVertex_fiber_op (unitCommaSource G)
    ((unitCommaSource G).app (Opposite.op ⦋0⦌)
      ((unitCommaSection η).app (Opposite.op ⦋0⦌) x))
    (unitCommaVertexInFiber G ((unitCommaSection η).app (Opposite.op ⦋0⦌) x)) (hη x)

end SerrePositivity.InfinityCategories
