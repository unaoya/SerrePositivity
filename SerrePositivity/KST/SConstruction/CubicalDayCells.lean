module
public import SerrePositivity.KST.SConstruction.CubicalDayTensor

/-! # 元の二つの cell による cubical Day tensor の表示
概要：元の連結 cell、その座標制限の関係式、射の判定と延長の普遍性を供給する。
方針：Day tensor の左 Kan 延長の単位と普遍性を、元の全立方体の成分で回収する。
規約：直積の二つの元から連結した次元の元を作る。使われ方：cubical 合成と鎖の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open scoped MonoidalCategory.ExternalProduct

/-- 元の二つの cell が Day tensor の連結立方体に定める元。 -/
def cubicalDayTensorCell {K L : CubicalSet.{u}} (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : K.obj (op c)) (y : L.obj (op d)) :
    (cubicalDayTensor K L).obj (op (concreteCubeTensorObj c d)) :=
  (cubicalDayTensorUnit K L).app (op c, op d) (x, y)

/-- 元の両立方体の射による制限は、Day tensor の同じ連結 cell の関係式を与える。 -/
lemma cubicalDayTensorCell_restrict {K L : CubicalSet.{u}} {c c' d d' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : c ⟶ c') (g : d ⟶ d') (x : K.obj (op c')) (y : L.obj (op d')) :
    (cubicalDayTensor K L).map (concreteCubeTensorMap f g).op
        (cubicalDayTensorCell c' d' x y) =
      cubicalDayTensorCell c d (K.map f.op x) (L.map g.op y) := by
  have h := (cubicalDayTensorUnit K L).naturality
    (show (op c', op d') ⟶ (op c, op d) from (f.op, g.op))
  exact (congrArg (fun t => t (x, y)) h).symm

/-- 元の全ての連結 cell の像は、Day tensor からの射を決定する。 -/
lemma cubicalDayTensor_cell_hom_ext {K L M : CubicalSet.{u}}
    {f g : cubicalDayTensor K L ⟶ M}
    (h : ∀ (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) (y : L.obj (op d)),
      f.app (op (concreteCubeTensorObj c d)) (cubicalDayTensorCell c d x y) =
        g.app (op (concreteCubeTensorObj c d)) (cubicalDayTensorCell c d x y)) : f = g := by
  apply cubicalDayTensor_hom_ext
  ext p z
  exact h p.1.unop p.2.unop z.1 z.2

/-- 二つの cell に対する自然な連結作用を、元の Day tensor 全体へ延長する。 -/
def cubicalDayTensorDesc {K L M : CubicalSet.{u}}
    (a : K ⊠ L ⟶ tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ ⋙ M) : cubicalDayTensor K L ⟶ M :=
  Functor.descOfIsLeftKanExtension _ (cubicalDayTensorUnit K L) _ a

/-- 元の延長は、指定した全ての連結 cell の作用を厳密に回収する。 -/
lemma cubicalDayTensorDesc_cell {K L M : CubicalSet.{u}}
    (a : K ⊠ L ⟶ tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ ⋙ M)
    (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) (y : L.obj (op d)) :
    (cubicalDayTensorDesc a).app (op (concreteCubeTensorObj c d))
        (cubicalDayTensorCell c d x y) = a.app (op c, op d) (x, y) :=
  congrArg (fun t => t (x, y))
    (Functor.descOfIsLeftKanExtension_fac_app _ (cubicalDayTensorUnit K L) _ a (op c, op d))

end SerrePositivity.KST.SConstruction
