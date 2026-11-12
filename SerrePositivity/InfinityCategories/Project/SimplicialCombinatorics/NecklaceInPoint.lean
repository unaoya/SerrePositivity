module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceWedgeStructure
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklacePostcomposition

/-! # 固定端点の元の一点 necklace
概要：K の任意の零単体に、両端を同じ点へ送る元の一点 necklace を与える。
方針：元の定値単体的写像を使い、零次数と入力後合成を照合する。
規約：高次の退化単体も保持。使われ方：cubical mapping object の合成の単位。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory Opposite _root_.Simplicial SSet

/-- 元の定値単体的写像は、零次数で指定した点を回収する。 -/
lemma simplicialConst_zero_apply {K L : SSet.{u}} (x : L _⦋0⦌) (s : K _⦋0⦌) :
    (SSet.const x : K ⟶ L).app _ s = x := by
  have h : (⦋0⦌.const ⦋0⦌ 0) = 𝟙 ⦋0⦌ := by
    ext i
    change 0 = i.val
    have hi := i.isLt
    change i.val < 1 at hi
    omega
  change L.map (⦋0⦌.const ⦋0⦌ 0).op x = x
  rw [h, op_id, L.map_id]
  rfl

/-- 元の点 x における、元の高次単体を持つ一点 necklace。 -/
def necklaceInPoint (K : SSet.{u}) (x : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x x where
  necklace := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint
  map := SSet.const x
  map_first := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialConst_zero_apply x _
  map_last := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialConst_zero_apply x _

/-- 元の一点 necklace の形は元の零長 necklace。 -/
lemma necklaceInPoint_necklace (K : SSet.{u}) (x : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x).necklace = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint := rfl

/-- 元の一点 necklace の K への写像は、元の全次数の定値写像。 -/
lemma necklaceInPoint_map (K : SSet.{u}) (x : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x).map = SSet.const x := rfl

/-- 入力の後合成は、元の一点 necklace の写像を厳密に保つ。 -/
lemma necklaceInPoint_postcompose_map {K L : SSet.{u}} (f : K ⟶ L) (x : K _⦋0⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose f x x).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x)).map =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint L (f.app _ x)).map := SSet.const_comp x f

/-- 元の一点の後合成と像の一点の間の、恒等 necklace 射による実可換三角形。 -/
def necklaceInPointPostcomposeHom {K L : SSet.{u}} (f : K ⟶ L) (x : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose f x x).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint L (f.app _ x) where
  necklaceHom := 𝟙 _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint
  w := by
    change 𝟙 _ ≫ SSet.const (f.app _ x) = SSet.const x ≫ f
    exact (Category.id_comp _).trans (SSet.const_comp x f).symm

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPoint := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPointPostcomposeHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPointPostcomposeHom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPointPostcomposeHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPoint_map := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint_map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPoint_necklace := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint_necklace

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPoint_postcompose_map := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint_postcompose_map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplicialConst_zero_apply := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialConst_zero_apply

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPoint._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPoint._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInPointPostcomposeHom._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPointPostcomposeHom._proof_1
