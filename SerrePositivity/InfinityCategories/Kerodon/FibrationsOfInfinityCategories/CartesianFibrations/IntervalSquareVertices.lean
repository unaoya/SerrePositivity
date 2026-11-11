module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IntervalSquare
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostIso

/-!
概要：同じ輸送四角形の四つの頂点を、指定した標準表示で正規化する。
方針：四辺の区間族を同じ等号で表示変更し、展開した元の四角形を厳密に保つ。
規約：底の四角形と全パラメーターを変更しない。
使われ方：元の Kan 合成四角形を既存の pointed-space の標準頂点で使う。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 四辺を同じ等号で正規化し、元の底の四角形は厳密に保つ。 -/
def TransportIntervalSquare.changeVertices {B P : SSet.{u}}
    {a b c d a' b' c' d' : B _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportIntervalSquare P a b c d)
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportIntervalSquare P a' b' c' d' where
  bottom := s.bottom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq (𝟙 B) a b ha hb
  top := s.top ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq (𝟙 B) c d hc hd
  left := s.left ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq (𝟙 B) a c ha hc
  right := s.right ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq (𝟙 B) b d hb hd
  square := s.square
  zero := s.zero.trans (by
    simpa only [Category.comp_id] using
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry (𝟙 B) a b ha hb s.bottom).symm)
  one := s.one.trans (by
    simpa only [Category.comp_id] using
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry (𝟙 B) c d hc hd s.top).symm)
  inner_zero := s.inner_zero.trans (by
    simpa only [Category.comp_id] using
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry (𝟙 B) a c ha hc s.left).symm)
  inner_one := s.inner_one.trans (by
    simpa only [Category.comp_id] using
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry (𝟙 B) b d hb hd s.right).symm)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
