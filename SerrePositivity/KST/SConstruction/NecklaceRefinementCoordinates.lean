module
public import SerrePositivity.KST.SConstruction.NecklaceRefinementNonjoint
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceNumericMap
public import SerrePositivity.KST.SConstruction.SimplexSubsetInclusionCoordinates

/-! # 元の refinement の右端からの数値座標
概要：元の非 joint 包含を右端から数値化し、元の順序・像・入力値を回収する。
方針：元の二つの反順列挙で、元の非 joint 頂点の恒等包含を挟む。
規約：元の局所頂点番号と因子順を保持。使われ方：分割合成の元の標準一面。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction

/-- 元の refinement の、同じ右端からの数値座標間の関数。 -/
def necklaceRefinementCoordinateFun (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    Fin T.down.dimension → Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).dimension :=
  fun i => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate.symm
    (necklaceRefinementNonjoint T (T.down.nonjointCoordinate i))

/-- 元の数値座標の包含は、元の同じ非 joint 頂点の包含を回収する。 -/
lemma necklaceRefinementCoordinate_recovery (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) (i : Fin T.down.dimension) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate
        (necklaceRefinementCoordinateFun T i) =
      necklaceRefinementNonjoint T (T.down.nonjointCoordinate i) :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate.apply_symm_apply _

/-- 元の右端からの数値座標の包含は、元の数値順序を厳密に保つ。 -/
lemma necklaceRefinementCoordinate_strictMono (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    StrictMono (necklaceRefinementCoordinateFun T) := by
  intro i j hij
  apply ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate_lt _ _).mp
  rw [necklaceRefinementCoordinate_recovery, necklaceRefinementCoordinate_recovery]
  exact (necklaceRefinementNonjoint T).strictMono ((T.down.nonjointCoordinate_lt j i).mpr hij)

/-- 元の refinement の、右端からの全数値座標の順序埋め込み。 -/
def necklaceRefinementCoordinate (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    Fin T.down.dimension ↪o Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).dimension :=
  OrderEmbedding.ofStrictMono (necklaceRefinementCoordinateFun T)
    (necklaceRefinementCoordinate_strictMono T)

/-- 元の数値座標の像は、元の necklace の joints を除いた同じ内部頂点の座標全体。 -/
lemma necklaceRefinementCoordinate_range (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    Set.range (necklaceRefinementCoordinate T) =
      {i | ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate i).val.val ∉
        T.down.joints} := by
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    change ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate
      (necklaceRefinementCoordinateFun T j)).val.val ∉ T.down.joints
    exact (congrArg (fun v => v.val.val ∉ T.down.joints)
      (necklaceRefinementCoordinate_recovery T j)).mpr (T.down.nonjointCoordinate j).property
  · intro h
    let v : T.down.NonjointVertex :=
      ⟨((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate i).val, h⟩
    refine ⟨T.down.nonjointCoordinate.symm v, ?_⟩
    apply (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate.injective
    exact (necklaceRefinementCoordinate_recovery T _).trans
      (congrArg (necklaceRefinementNonjoint T) (T.down.nonjointCoordinate.apply_symm_apply v))

/-- 元の数値座標包含の像では、元の refinement cube 射は同じ入力値を保つ。 -/
lemma necklaceRefinementCoordinate_numeric (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex T.down.dimension)
    (i : Fin T.down.dimension) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap (necklaceBeadRefinement T) x (necklaceRefinementCoordinate T i) = x i := by
  have h := necklaceBooleanMap_nonjoint_of_injective (necklaceBeadRefinement T) (fun _ _ h => h)
    (fun v => x (T.down.nonjointCoordinate.symm v)) (T.down.nonjointCoordinate i)
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single T.down.vertexMax).nonjointCoordinate (necklaceRefinementCoordinate T i))
    (congrArg Subtype.val (necklaceRefinementCoordinate_recovery T i)).symm
  exact h.trans (congrArg x (T.down.nonjointCoordinate.symm_apply_apply i))

end SerrePositivity.KST.SConstruction
