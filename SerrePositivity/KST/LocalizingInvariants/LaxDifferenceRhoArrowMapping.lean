module

public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceRhoTargetMapping
public import SerrePositivity.KST.LocalizingInvariants.TensorHomotopyEquivalence
public import SerrePositivity.KST.LocalizingInvariants.KanFibrationEquivalenceBaseChange
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackMappingProductSquare
public import SerrePositivity.InfinityCategories.F2.CatInfinity.KanTensorComplex

/-!
概要：ρ(y) への写像空間の元の lax 矢印関手による比較は同値。
方針：C・D 二辺の積の同値を、元の端点評価の Kan fibration に沿って引き戻す。
規約：元の pinchedHomMap と正方形を保持。使われ方：Tamme Prop. 11 の cofiber 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
local instance rhoArrowMappingTensorKan (A B : SSet.{u}) [KanComplex A] [KanComplex B] :
    KanComplex (A ⊗ B) := F2.kanComplex_tensor A B

variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (v : E.obj ⟶ D.obj) (a : QCatAdjunction q.hom v) (hv : IsFullyFaithful v)

include a hv in
lemma laxDifferenceRho_arrowMapping_equivalence (x : (laxCategory p q).obj _⦋0⦌)
    (y : E.obj _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap (F2.laxPullbackArrow p.hom q.hom) x
      ((laxDifferenceRho p q v).app (Opposite.op ⦋0⦌) y)) := by
  have : Fibration (F2.laxPullbackMappingEndpointMap p.hom q.hom x
      ((laxDifferenceRho p q v).app (Opposite.op ⦋0⦌) y)) := inferInstance
  apply kanPullback_first_equivalence
    (F2.laxPullbackMappingProduct_isPullback p.hom q.hom x
      ((laxDifferenceRho p q v).app (Opposite.op ⦋0⦌) y))
  exact tensor_simplicialHomotopyEquivalence
    (laxDifferenceRho_fstMapping_equivalence p q v x y)
    (laxDifferenceRho_sndMapping_equivalence p q v a hv x y)

end SerrePositivity.KST.LocalizingInvariants
