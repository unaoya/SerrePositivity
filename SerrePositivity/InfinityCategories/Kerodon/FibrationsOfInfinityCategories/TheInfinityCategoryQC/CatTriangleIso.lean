module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTriangleEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatHomPostcomposition

/-!
概要：Cat_∞ の任意の二単体を指定された関手同型として読み戻す。
方針：豊穣 Hom の精密化の像を core Fun へ移し、その辺の類で同型を作る。
規約：辺の代表を選び直さず、元の二単体の一単体の像を保つ。
使われ方：引き戻し錐の native な可換性と指定 path の比較。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：QCat の豊穣頂点を含めると指定関手の頂点に一致する。
方針：豊穣単位からの表示を零単体で評価する。
規約：指定関手自体を厳密に保持する。
使われ方：core Fun の指定辺の両端を関手の頂点に合わせる。 -/
lemma qCatHom_vertex_ι (A B : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (f : A ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom A.obj).obj B.obj)).ι.app (Opposite.op ⦋0⦌)
      (SimplicialCategory.homEquiv' A B f) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show A.obj ⟶ B.obj from f) := by
  exact congrArg (SSet.unitHomEquiv ((ihom A.obj).obj B.obj)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatHom_unit_ι A B f)
/-- 概要：Cat_∞ の二単体を関手単体集合の指定辺にする。
方針：豊穣 Hom の精密化の像を core の包含で写す。
規約：長辺から二辺の合成へ向く元の一単体を保持する。
使われ方：native な三角形の可換性を実際の関手同型へ送る。 -/
def catInfinityTriangleEdge (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋2⦌) :
    ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 2⟩).obj).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 1 s)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 2 s) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 0 s))) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleEdge s).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 2⟩).obj)).ι).ofEq
      (qCatHom_vertex_ι _ _ _) (qCatHom_vertex_ι _ _ _)
/-- 概要：Cat_∞ の二単体から読み戻した関手の辺は可逆。
方針：QCat の豊穣 Hom の Kan 性から得た可逆性を core の包含で保つ。
規約：指定辺を別の辺で置き換えない。
使われ方：元の辺の類を順方向の射とする関手同型の構成。 -/
lemma catInfinityTriangleEdge_isInvertible (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋2⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (catInfinityTriangleEdge s).toTruncated := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleEdge s).toTruncated :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex _)
  have h' := h.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 2⟩).obj)).ι
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleEdge s).toTruncated.map
    ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 2⟩).obj)).ι)))
    (f := (catInfinityTriangleEdge s).toTruncated) rfl).mp h'
/-- 概要：Cat_∞ の二単体を長辺と二辺の合成の指定関手同型へ送る。
方針：読み戻した可逆辺のホモトピー圏の類に asIso を適用する。
規約：同型の順方向の射は元の三角形の精密化の像の類。
使われ方：引き戻し錐の native な可換性の読み戻し。 -/
def catInfinityTriangleIso (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋2⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 1 s))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 2 s) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 0 s)) := by
  have := catInfinityTriangleEdge_isInvertible s
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (catInfinityTriangleEdge s).toTruncated)
/-- 概要：三角形の関手同型の順方向の射は指定辺の類。
方針：asIso の順方向の射の定義を読む。
規約：関手同型の存在だけに弱めず元の類を記録する。
使われ方：指定 path と native な可換性の照合。 -/
lemma catInfinityTriangleIso_hom (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋2⦌) :
    (catInfinityTriangleIso s).hom =
      SSet.Truncated.HomotopyCategory.homMk (catInfinityTriangleEdge s).toTruncated := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
