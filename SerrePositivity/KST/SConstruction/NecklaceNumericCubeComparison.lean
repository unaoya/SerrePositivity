module
public import SerrePositivity.KST.SConstruction.NecklaceConcreteCube
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceBooleanFunctor

/-! # 元の部分集合関手と具体的立方体関手の頂点作用の自然な比較
概要：元の全 necklace 射の具体的 cube 作用が同じ部分集合像を回収すると証明する。
方針：右端列挙の元の同値で数値座標を比較し、両逆律で自然性を得る。
規約：選んだ別の cube 射へ置換しない。使われ方：cubical rigidification の原典との照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
namespace NecklaceShape

/-- 元の非 joint Bool 座標と、同じ次元の右端からの数値立方体の順序同型。 -/
def numericCubeIso (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : (T.NonjointVertex → Bool) ≃o _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex T.dimension where
  toFun b := fun i => b (T.nonjointCoordinate i)
  invFun x := fun v => x (T.nonjointCoordinate.symm v)
  left_inv b := funext (fun v => congrArg b (T.nonjointCoordinate.apply_symm_apply v))
  right_inv x := funext (fun i => congrArg x (T.nonjointCoordinate.symm_apply_apply i))
  map_rel_iff' := by
    intro b c
    change (∀ i, b (T.nonjointCoordinate i) ≤ c (T.nonjointCoordinate i)) ↔ ∀ v, b v ≤ c v
    constructor
    · intro h v
      obtain ⟨i, rfl⟩ := T.nonjointCoordinate.surjective v
      exact h i
    · intro h i
      exact h _

end NecklaceShape

/-- 既存の具体的 cube と同じ全頂点・同じ生成関数を持つ順序集合値関手。 -/
def concreteCubeOrderedVertices : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube ⥤ PartOrd where
  obj T := PartOrd.of (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex T.dimension)
  map f := PartOrd.ofHom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeMapGeneratedOrderHom f.property)
  map_id _ := PartOrd.Hom.ext rfl
  map_comp _ _ := PartOrd.Hom.ext rfl

/-- 元の necklace の Bool 座標作用と、同じ具体的 cube 射の全頂点作用との自然同型。 -/
def necklaceBooleanNumericNatIso : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanPoset.{u} ≅
    necklaceConcreteCube ⋙ concreteCubeOrderedVertices :=
  NatIso.ofComponents (fun T => PartOrd.Iso.mk (_root_.SerrePositivity.KST.SConstruction.NecklaceShape.numericCubeIso T.down)) (by
    intro T U f
    apply PartOrd.Hom.ext
    apply DFunLike.ext
    intro b
    funext j
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap f b (U.down.nonjointCoordinate j) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap f
        (fun v => b (T.down.nonjointCoordinate (T.down.nonjointCoordinate.symm v)))
        (U.down.nonjointCoordinate j)
    simp only [Equiv.apply_symm_apply])

/-- 原典の全 joints を含む部分集合像は、元の具体的 cube 関手の全頂点作用と一致する。 -/
def necklaceSubsetNumericNatIso : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSubsetPoset.{u} ≅
    necklaceConcreteCube ⋙ concreteCubeOrderedVertices :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSubsetBooleanNatIso ≪≫ necklaceBooleanNumericNatIso

end SerrePositivity.KST.SConstruction
