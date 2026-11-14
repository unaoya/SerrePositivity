module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationConnecting
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableOpposite

/-! # Cofiber 列の前の列

概要：任意の cofiber 列の第一射を第二射に持つ cofiber 列を双対回転で構成する。
方針：反対圏で回転し、零角を保つ双対化で元の圏へ戻す。
規約：第二射の一致は単体的な辺の等号で保持する。使われ方：三角形の逆回転への閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：単体を二度反転して二重反対を戻すと元の射になる。
方針：各次数の頂点順序の二重反転を計算する。
規約：単体の次数は任意。使われ方：双対回転の第二射の照合。 -/
lemma stableReverseSimplex_double {X : SSet.{u}} (n : ℕ) (F : (Δ[n] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex n F) ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom = F := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change F.app _ _ = F.app _ s
  congr 1
  apply stdSimplex.ext
  intro i
  change ((s i.rev.rev).rev).rev = s i
  simp

/-- 概要：零角の列を双対化して反対圏の零角の列とする。
方針：二座標の交換反転で零角の位置を保つ。
規約：追加の充填性の仮定なし。使われ方：cofiber 列の双対回転。 -/
def ZeroTriangle.op {X : SSet.{u}} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X.op where
  square := _root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare t.square
  zero_corner := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare_vertex]
    exact t.zero_corner.op

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (op)


/-- 概要：安定な quasicategory の cofiber 列の双対も cofiber 列となる。
方針：元の列を fiber 列とみなし、双対の押し出し性を得る。
規約：零角を持つ列に安定性を使う。使われ方：反対圏で回転長方形を選ぶ。 -/
lemma ZeroTriangle.op_isCofiber {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t.op :=
  (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_dualSquare t.square).1 ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.fiber_iff_cofiber t).2 ht)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (op_isCofiber)


/-- 概要：反対圏の零角の列を元の圏の零角の列へ戻す。
方針：双対四角形の後で二重反対の同型を合成する。
規約：元の頂点の表示を使う。使われ方：逆回転列の構成。 -/
def ZeroTriangle.unop {X : SSet.{u}} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X.op) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X where
  square := _root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare t.square ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
  zero_corner := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := X) (SSet.opObjEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 1))
    exact t.zero_corner.unop

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (unop)


/-- 概要：反対圏の cofiber 列を戻しても cofiber 列となる。
方針：双対の引き戻し性を同型で戻し、安定性で押し出し性へ移す。
規約：元の圏が安定。使われ方：前の cofiber 列の普遍性。 -/
lemma ZeroTriangle.unop_isCofiber {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X.op) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t.unop := by
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.fiber_iff_cofiber t.unop).1
  exact (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_postcomp_isIso (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare t.square)
    (SSet.opFunctorCompOpFunctorIso.app X).hom).1
      ((_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPushoutSquare_iff_dualSquare t.square).1 ht)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (unop_isCofiber)


/-- 概要：任意の cofiber 列の第一射を第二射に持つ cofiber 列が存在する。
方針：反対圏で回転した右面を双対化して戻し、共有辺と二重反転で第二射を計算する。
規約：辺は単体的な射として厳密に一致。使われ方：TR2 の逆方向の幾何学的入力。 -/
lemma exists_cofiberPredecessor {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence d ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ d.square = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square := by
  let r := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberRotationRectangle t.op (t.op_isCofiber ht)
  refine ⟨r.rotatedZeroTriangle.unop, r.rotatedZeroTriangle.unop_isCofiber r.rotated_isCofiber, ?_⟩
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ r.rotatedZeroTriangle.square = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ t.op.square := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ t.op.square
    rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_sharedEdge, r.left_eq]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare r.rotatedZeroTriangle.square ≫ _) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare_rightEdge, he]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare t.square) ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare_rightEdge, stableReverseSimplex_double]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
