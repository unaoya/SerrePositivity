module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanConeRelativeForget
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanConeValuePath

/-!
概要：底固定の指定可換円柱の類を元の全空間・単位上の指定比較へ戻す。
方針：相対同型の忘却の等式と円柱の代表の仕様、後合成の作用を使う。
規約：元の指定類を保持。使われ方：Kan 延長後の path と native 比較候補の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)

/-- 概要：底固定円柱は元の左右三角形からの全空間の指定可換同型を表す。
方針：相対同型の忘却の等式。規約：同じ指定類。使われ方：既存の円柱との照合。 -/
lemma coherentCospanConeRelativePathHomotopy_total_hom :
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (coherentCospanConeRelativePathHomotopy F X Y Z C)) =
        (coherentCospanConeTotalPathIso F X Y Z C).hom := by
  rw [coherentCospanConeRelativePathHomotopy_hom, coherentCospanConeRelativePathIso_forget]

/-- 概要：単位上で底固定円柱と既存の全空間円柱は同じ指定可換類を持つ。
方針：元の両円柱の類の一致を単位の後合成で写す。
規約：元の指定値。使われ方：Kan 置換後の全 path 比較への入力。 -/
lemma coherentCospanConeRelativePathHomotopy_unit_hom :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (coherentCospanConeRelativePathHomotopy F X Y Z C)
        (continuousKanReplacementUnit.app (smallLeftUnstraightening Z)))) =
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (coherentCospanConeTotalPathHomotopy F X Y Z C)
        (continuousKanReplacementUnit.app (smallLeftUnstraightening Z)))) := by
  rw [functorHomotopyPostcomp_hom, functorHomotopyPostcomp_hom,
    coherentCospanConeRelativePathHomotopy_total_hom, coherentCospanConeTotalPathHomotopy_hom]

end SerrePositivity.InfinityCategories.F2
