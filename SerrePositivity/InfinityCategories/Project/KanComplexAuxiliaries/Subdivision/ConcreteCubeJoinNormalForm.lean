module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.ConcreteCubeSignature
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Cubes.CubeJoinNormalForm

/-! # 具体的な cubical 射の有限 max 正規形
概要：生成条件を保つ元の射を、一意な有限 max 表示へ単射で送る。
方針：join 保存による全頂点の回収式を適用し、合成も同じ評価から計算する。
規約：全ての有限 max 表示が cubical 射であるとは主張しない。
使われ方：具体的な立方体圏と Serre 鎖立方体の表示非依存性の比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の具体的な cubical 射から回収した有限 max 表示。 -/
def concreteCubeNormalForm {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm X.dimension Y.dimension :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormOfMap f.val

/-- 元の cubical 射は、同じ射の有限 max 表示を評価して回収される。 -/
lemma concreteCubeNormalForm_eval {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex X.dimension) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f) x = f.val x :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormOfMap_eval (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeMapGenerated_sup f.property) x

/-- 有限 max 表示は具体的な cubical 射の等号を検出する。 -/
lemma concreteCubeNormalForm_injective (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm (X := X) (Y := Y)) := by
  intro f g h
  apply Subtype.ext
  funext x
  rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_eval f x, ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_eval g x, h]

/-- 具体的な cubical 射の等号と、同じ有限 max 表示の等号の同値。 -/
lemma concreteCubeNormalForm_eq_iff {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f g : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm g ↔ f = g :=
  (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_injective X Y).eq_iff

/-- 元の合成の有限 max 表示は、同じ二つの表示の評価の合成から回収される。 -/
lemma concreteCubeNormalForm_comp {X Y Z : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) (g : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm (f ≫ g) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormOfMap
      (fun x => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm g)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f) x)) := by
  apply congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormOfMap
  funext x
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_eval, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_eval]
  rfl

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
