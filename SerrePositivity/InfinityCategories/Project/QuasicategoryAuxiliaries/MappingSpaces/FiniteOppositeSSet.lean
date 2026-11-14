module
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-!
概要：有限極限から反対圏の同じ有限図式の余極限を構成する。
方針：非退化単体の反転同値と、元の図式を回収する二重反転を使う。
規約：元の圏の有限余極限は結論しない。使われ方：一般安定性判定の双対化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 同じ有限図式と極限錐を反転して普遍余錐を得る。 -/
instance finite_opposite_sset {K : SSet.{u}} [K.Finite] : K.op.Finite where
  finite := Finite.of_equiv K.N (SSet.N.opEquiv (X := K)).symm.toEquiv

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
