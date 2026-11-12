module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsomorphismCofiberZero

/-! # 完全関手による指定辺の cofiber の像

概要：完全関手は指定した実辺の cofiber 四角形をその像の cofiber 四角形へ送る。
方針：零角と押し出し性を保存し、底辺を Yoneda の自然性で照合する。
規約：実四角形と指定辺を保持。使われ方：零化と辺の反転の同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X Y : SSet.{u}} (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F]
variable {x y : X _⦋0⦌} {f : Truncated.Edge (X := (truncation 2).obj X) x y}

/-- 完全関手は、指定した実辺と全四角形を保って cofiber を写す。 -/
def CofiberSquare.map (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare (f.map ((truncation 2).map F)) where
  toZeroTriangle := s.toZeroTriangle.map F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F))
  bottom_edge := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (s.square ≫ F) = _
    rw [← Category.assoc, s.bottom_edge, SSet.yonedaEquiv_symm_comp]
    rfl
  isPushout := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := F) s.toZeroTriangle s.isPushout

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquare (map)


/-- 写した cofiber 対象は、元の実 cofiber 頂点の関手像である。 -/
lemma CofiberSquare.map_cofiber (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f) :
    (s.map F).cofiber = F.app (Opposite.op ⦋0⦌) s.cofiber := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquare (map_cofiber)


/-- 完全関手が辺を反転することと、その実 cofiber を零化することは同値。 -/
lemma CofiberSquare.map_isInvertible_iff_zero [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (f.map ((truncation 2).map F)) ↔
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) s.cofiber) :=
  (s.map F).homMk_isIso_iff_zero

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquare (map_isInvertible_iff_zero)


end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
