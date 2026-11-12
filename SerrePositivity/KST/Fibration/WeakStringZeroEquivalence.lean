module
public import SerrePositivity.KST.Fibration.WeakStringVertices
public import SerrePositivity.KST.Fibration.WeakArrowEndpointExact
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FullSubcomplexIso

/-! # 零長の元の W 列と同じ全頂点部分圏の完全な厳密同型 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の一点評価の同型を、零長 W 列と全頂点部分圏の同型へ制限する。 -/
def weakStringZeroIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakStringCategory q ⦋0⦌ ≅
      closedSubcategory (ClosedStablePredicate.top (sInputModel B)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso (SConstruction.pointFunctorEvaluationIso B.obj) (weakStringPredicate q ⦋0⦌)
    (ClosedStablePredicate.top (sInputModel B)).predicate
    (fun v => ⟨fun _ => trivial, fun _ => weakStringPredicate_zero q v⟩)

/-- 同じ順射は、既存の零長の初期頂点の完全評価そのもの。 -/
lemma weakStringZeroIso_hom {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (weakStringZeroIso q).hom = (weakStringVertexTopExact q ⦋0⦌ 0).val := rfl

/-- 零長の初期頂点評価を順射とする、元の安定な入力の厳密同型。 -/
def weakStringZeroExactIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakStringModel q ⦋0⦌ ≅
      closedStableModel (ClosedStablePredicate.top (sInputModel B)) := by
  let e := weakStringZeroIso q
  have hi := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).symm.isQCatEquivalence
  exact {
    hom := weakStringVertexTopExact q ⦋0⦌ 0
    inv := ⟨e.inv, hi.preservesZero, hi.preservesCofiber⟩
    hom_inv_id := Subtype.ext e.hom_inv_id
    inv_hom_id := Subtype.ext e.inv_hom_id }

end SerrePositivity.KST.Fibration
