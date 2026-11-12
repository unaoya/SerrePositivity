module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn

/-! # 単体集合の写像による元の necklace の後合成
概要：K 内の全 necklace を L 内へ送り、元の全可換三角形を保持する。
方針：元の実単体的写像に後合成し、両端点と図式の式をそのまま回収する。
規約：necklace の形と射を変えない。使われ方：cubical rigidification の入力関手性。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 元の単体集合の射による、すべての necklace の後合成関手。 -/
def necklaceInPostcompose {K L : SSet.{u}} (f : K ⟶ L) (x y : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y ⥤ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn L (f.app _ x) (f.app _ y) where
  obj T :=
    { necklace := T.necklace
      map := T.map ≫ f
      map_first := by
        change f.app _ (T.map.app _ T.necklace.down.firstVertex) = _
        rw [T.map_first]
      map_last := by
        change f.app _ (T.map.app _ T.necklace.down.lastVertex) = _
        rw [T.map_last] }
  map g :=
    { necklaceHom := g.necklaceHom
      w := by
        change g.necklaceHom.map ≫ _ ≫ f = _ ≫ f
        rw [← Category.assoc, g.w] }
  map_id _ := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext rfl
  map_comp _ _ := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext rfl

/-- 後合成しても、元のすべての necklace の形と射の図式を厳密に回収する。 -/
lemma necklaceInPostcompose_forget {K L : SSet.{u}} (f : K ⟶ L) (x y : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose f x y ⋙ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInForget L (f.app _ x) (f.app _ y) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInForget K x y := rfl

/-- 後合成先の元の単体的 necklace 写像は、元の写像と同じ射の合成。 -/
lemma necklaceInPostcompose_obj_map {K L : SSet.{u}} (f : K ⟶ L) (x y : K _⦋0⦌)
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) :
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose f x y).obj T).map = T.map ≫ f := rfl

/-- 後合成先の全可換三角形は、元の necklace 射を厳密に保持する。 -/
lemma necklaceInPostcompose_map {K L : SSet.{u}} (f : K ⟶ L) (x y : K _⦋0⦌)
    {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y} (g : T ⟶ U) :
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose f x y).map g).necklaceHom = g.necklaceHom := rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPostcompose := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPostcompose_forget := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose_forget

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPostcompose_map := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose_map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPostcompose_obj_map := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose_obj_map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPostcompose._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPostcompose._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPostcompose._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPostcompose._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPostcompose._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPostcompose._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPostcompose._proof_7 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose._proof_7
