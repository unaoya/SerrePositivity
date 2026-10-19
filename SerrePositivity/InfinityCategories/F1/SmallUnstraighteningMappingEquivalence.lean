module

public import SerrePositivity.InfinityCategories.F1.UnstraighteningFamilyWitnessRestriction
public import SerrePositivity.InfinityCategories.F1.SmallUnstraighteningMappingRetraction
public import SerrePositivity.InfinityCategories.F1.CoherentTransformationSmallness
public import SerrePositivity.InfinityCategories.F1.CoherentUnstraighteningMappingEquivalence

/-!
概要：小さい底上の coherent な図式の unstraightening の写像空間比較は同値。
方針：普遍的な相対射の族を復元しその証拠を制限して両側の関手同型を得る。
規約：底は各次数で小さく strict な図式への制限は不要。
使われ方：Kerodon Corollary 5.6.0.6 の小さい底上の写像空間比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：小さい底上の unstraightening の実際の写像空間比較は同値。
方針：普遍的な射の族の復元と同じ射を表す二つの証拠の一意性を使う。
規約：一般の非可逆変換と全高次パラメーターを含む。
使われ方：straightening の写像空間比較の小さい底の場合の主定理。 -/
lemma small_leftUnstraighteningMappingSpaceMap_isQCatEquivalence
    {B : SSet.{u + 1}} [∀ n, Small.{u} (B.obj n)] (F G : B ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (leftUnstraighteningMappingSpaceMap F G) :=
  leftUnstraighteningMappingSpaceMap_isQCatEquivalence F G

end SerrePositivity.InfinityCategories
