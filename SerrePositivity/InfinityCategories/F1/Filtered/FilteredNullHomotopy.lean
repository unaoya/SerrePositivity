module
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.FilteredNullHomotopy
public import SerrePositivity.InfinityCategories.Core.Filtered.FilteredInfinity


/-!
概要：余錐は元の図式から定値図式への実際のホモトピーを与える。
方針：余錐を頂点の slice の図式とみなし、既存の円柱比較を使う。
規約：余錐の頂点も元の図式も変更しない。
使われ方：filtered ∞ 圏の有限図式の収縮を Kan 置換へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：filtered ∞ 圏の全ての有限図式はある定値図式にホモトピック。
方針：filtered 性から余錐を取り、その指定頂点への収縮を使う。
規約：K は任意の有限単体集合。使われ方：一般の弱可縮性の有限検査。 -/
lemma exists_nullHomotopy_of_isFilteredInfinity {K C : SSet.{u}}
    [Quasicategory C] [IsFilteredInfinity C] [K.Finite] (p : K ⟶ C) :
    ∃ x : C _⦋0⦌, Nonempty (SSet.Homotopy p (SSet.const x)) := by
  obtain ⟨c⟩ := IsFilteredInfinity.cocone_nonempty p
  exact ⟨c.vertex, ⟨coconeNullHomotopy c⟩⟩

end SerrePositivity.InfinityCategories.F2
