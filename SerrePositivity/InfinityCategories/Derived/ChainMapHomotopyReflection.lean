module
public import SerrePositivity.InfinityCategories.Derived.FullInclusionHomotopyObjects
public import SerrePositivity.InfinityCategories.Derived.ChainMapEdge
public import SerrePositivity.InfinityCategories.Stable.ArrowFaithfulReflection

/-! # 包含後の辺から鎖写像の h の類を反映する

概要：端点表示を含む辺の類を、全複体への包含後の一単体から同定する。
方針：包含の忠実性と対象での単射性を使う。
規約：元の辺の端点を保持する。使われ方：D7 の標準列の第一・第二射。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {S : Type u} [CommRing S]

/-- 包含後に鎖写像の辺と一致する辺は、h 上でもその鎖写像の類になる。 -/
lemma derived_homMk_arrow_eq_of_inclusion
    {x y : (derivedInfinityCategory S) _⦋0⦌} {X Y : Semifree S}
    (e : Truncated.Edge (X := DGNerve.HomotopyComparison.twoTruncation S (Semifree S)) x y)
    (a : X.val ⟶ Y.val)
    (he : (e.map ((SSet.truncation 2).map derivedInfinityInclusion)).edge =
      (complexEdge a).edge) :
    Arrow.mk (Truncated.HomotopyCategory.homMk e) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (derivedChainMapEdge (x := Simplex.vertex X) (y := Simplex.vertex Y) a)) := by
  let : (hoFunctor.map (derivedInfinityInclusion (S := S))).toFunctor.Faithful :=
    fullInclusionHo_faithful S (Complex S) (complexSemifree S)
  apply arrowMk_eq_of_faithful_map (hoFunctor.map derivedInfinityInclusion).toFunctor
    (fullInclusionHo_obj_injective S (Complex S) (complexSemifree S))
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact he.trans (derivedChainMapEdge_inclusion
    (x := Simplex.vertex X) (y := Simplex.vertex Y) a).symm

end SerrePositivity.InfinityCategories
