module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap

/-!
概要：右写像空間の端点の等式による同型。
方針：端点の等式を消去し元の pinched 単体の値を保持する。
規約：元の頂点と pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の写像空間の引き戻し正方形。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：右写像空間の端点の等式による同型。
方針：端点の等式を消去し元の pinched 単体の値を保持する。
規約：元の頂点と右写像空間の単体の値を保持する。
使われ方：原典の写像空間の四角形への厳密な輸送。 -/
def pinchedHomIsoOfEq {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x' y' := by
  subst x'
  subst y'
  exact Iso.refl _
/-- 概要：右写像空間の端点の等式による同型。
方針：端点の等式を消去し元の pinched 単体の値を保持する。
規約：元の頂点と右写像空間の単体の値を保持する。
使われ方：原典の写像空間の四角形への厳密な輸送。 -/
lemma pinchedHomIsoOfEq_hom_val {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') (n : ℕ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) _⦋n⦌) :
    ((pinchedHomIsoOfEq hx hy).hom.app (Opposite.op ⦋n⦌) s).val = s.val := by
  subst x'
  subst y'
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
