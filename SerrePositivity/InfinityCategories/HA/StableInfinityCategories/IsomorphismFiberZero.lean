module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsomorphismCofiberZero
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableOpposite

/-! # 同型射の fiber の消滅

概要：同型射の fiber は零であり、安定な場合には零 fiber による同型判定が同値となる。
方針：指定した fiber 四角形を反対の単体集合の cofiber 四角形に双対化する。
規約：fiber の選択は任意。使われ方：比較射の fiber による同型判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：fiber 四角形を双対化すると反転した辺の cofiber 四角形となる。
方針：四角形の双対で零角と指定辺を照合し、普遍性を移す。
規約：安定性は不要。使われ方：fiber と cofiber の消滅判定の双対化。 -/
def FiberSquare.opCofiber {X : SSet.{u}}
    {x y : X _⦋0⦌} {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare f) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (X := X.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp f) where
  square := _root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare s.square
  zero_corner := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare_vertex]
    exact s.zero_corner.op
  bottom_edge := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare_bottomEdge, s.right_edge]
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.reverseSimplex_edgeUnop (X := X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp f)
  isPushout := (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_dualSquare s.square).1 s.isPullback

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FiberSquare (opCofiber)


/-- 概要：指定された同型辺の任意の fiber は零である。
方針：反対側の cofiber の消滅を元の単体集合に戻す。
規約：値域は quasicategory、安定性は不要。使われ方：fiber の消滅による判定の逆向き。 -/
lemma FiberSquare.zero_of_homMk_isIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare f) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge f) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex s.fiber := by
  exact (s.opCofiber.zero_of_homMk_isIso hi.op).unop

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FiberSquare (zero_of_homMk_isIso)


/-- 概要：安定な場合、指定辺が同型であることと任意の選んだ fiber が零であることは同値。
方針：同型からの消滅と、零 fiber からの同型判定を組み合わせる。
規約：fiber 四角形の選択は固定してもよい。使われ方：比較射の同型判定。 -/
lemma FiberSquare.homMk_isIso_iff_zero {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x y : X _⦋0⦌} {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare f) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge f ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex s.fiber :=
  ⟨s.zero_of_homMk_isIso, s.homMk_isIso_of_zero⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FiberSquare (homMk_isIso_iff_zero)


end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
