module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantTargetValueProjectionTo
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantUnstraighteningValueOverPre

/-!
概要：固定値への定値相対射影と、元の底上の射による前合成の厳密な可換性。
方針：指定頂点等式だけを消去し、全係数の元の値射影の自然性を使う。
規約：元の底上の射と固定値を保持。使われ方：五因子式の最後の比較の前合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ指定固定値への射影は、元の底上の射による前合成と全族で厳密に可換する。 -/
lemma constantTargetValueProjectionTo_overPre {A C B : SSet.{u + 1}}
    (p : A ⟶ B) (d : C ⟶ B) (t : C ⟶ A) (ht : t ≫ p = d)
    {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z') :
    relativeFunctorOverPre (leftUnstraighteningProjection (SSet.const z : B ⟶ SpaceInfinity))
        (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht) ≫
      constantTargetValueProjectionTo d hz = constantTargetValueProjectionTo p hz ≫
        (pre t).app ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z').obj) := by
  cases hz
  exact constantUnstraighteningRelativeIso_value_overPre p d t ht z

end SerrePositivity.InfinityCategories.F2
