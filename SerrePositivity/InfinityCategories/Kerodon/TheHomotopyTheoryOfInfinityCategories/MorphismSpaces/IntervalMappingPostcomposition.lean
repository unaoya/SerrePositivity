module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingSpace

/-!
概要：両端固定の区間写像空間の標的への後合成。
方針：区間の普遍的な族に後合成してから相対 curry する。
規約：標的の充填性を仮定せず、固定端点も射で写す。
使われ方：Kerodon §4.6.6（Tag 04HY）、coherent diagram の制限による変換の写像空間への作用。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：固定した二端点の境界図式は標的への射と可換。
方針：境界の各単体で端点に場合分けし、定値射の自然性を使う。
規約：二端点が一致する場合も含む。
使われ方：Kerodon §4.6.6（Tag 04HY）、区間模型の後合成の境界条件。 -/
lemma intervalMappingBoundary_post {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y ≫ f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary (f.app _ x) (f.app _ y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change f.app (Opposite.op ⦋n⦌) (if s.val 0 = 0 then _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n
    else _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y n) =
      if s.val 0 = 0 then _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (f.app _ x) n
      else _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (f.app _ y) n
  split
  · exact f.naturality_apply (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op x
  · exact f.naturality_apply (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op y

/-- 概要：単体集合の射は両端固定の区間写像空間の射を誘導する。
方針：普遍的な区間の族へ後合成し、写された境界条件で curry する。
規約：端点は標的の射の零単体での作用で写す。
使われ方：Kerodon §4.6.6（Tag 04HY）、区間模型の写像空間の共変性。 -/
def intervalMappingPost {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (f.app _ x) (f.app _ y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y)) ≫ f) (by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_boundary,
      Category.assoc, intervalMappingBoundary_post])

/-- 概要：区間写像空間の後合成の評価は、元の区間の族への後合成。
方針：パラメーター自然性と curry の往復を使う。
規約：任意のパラメーター T からの族を扱う。
使われ方：Kerodon §4.6.6（Tag 04HY）、後合成の写像空間での計算則。 -/
lemma intervalMappingPost_uncurry {T X Y : SSet.{u}}
    (f : X ⟶ Y) (x y : X _⦋0⦌) (g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (g ≫ intervalMappingPost f x y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g ≫ f := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, intervalMappingPost,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curry, ← Category.assoc]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp g (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y))
  rw [Category.comp_id] at h
  rw [← h]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
