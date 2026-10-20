module
public import SerrePositivity.InfinityCategories.Derived.DGInvertingHomNaturality
public import SerrePositivity.InfinityCategories.Derived.WeakRoofDescentSpace

/-! # 任意の反転関手の実 Hom 降下の高次選択空間

概要：各対象対について、屋根評価と商 Hom への降下の全高次族は可縮な空間をなす。
方針：任意標的の固定 Hom 包含と実商屋根比較の弱同値を、二段降下空間へ代入する。
規約：異なる対象対の合成の coherent な両立はまだ主張しない。
使われ方：局所化の普遍性の写像空間データの高次の選択。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 任意標的への Hom 降下を、両比較を保つ高次族として表す空間。 -/
def dgInvertingHomDescentSpace (P : Set D) (x y : D) {Y : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) : SSet.{max u v} :=
  weakRoofDescentSpace (dgRoofCorrespondenceMap A D P x y)
    (dgInvertingFixedHomRoofMap A D P x F (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
    (dgInvertingRoofFunctorMap A D P x y F)

/-- 各対象対の全高次の降下データは、全境界を充填する可縮 Kan 複体。 -/
theorem dgInvertingHomDescentSpace_isContractibleKan (P : Set D)
    (hP : DGQuotient.localKFlat A D P) (x y : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P)) :
    IsContractibleKan (dgInvertingHomDescentSpace A D P x y F) :=
  weakRoofDescentSpace_isContractibleKan
    (dgRoofCorrespondenceMap_isWeakHomotopyEquivalence A D P hP x y)
    (dgInvertingFixedHomRoofMap_isWeakHomotopyEquivalence A D P x F hF
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
    (dgInvertingRoofFunctorMap A D P x y F)

end SerrePositivity.InfinityCategories
