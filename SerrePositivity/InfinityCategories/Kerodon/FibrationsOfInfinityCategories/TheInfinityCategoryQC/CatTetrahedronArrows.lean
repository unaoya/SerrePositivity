module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentEdges

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorWhiskerSimplex

/-!
概要：Cat_∞ の三単体の六辺の関手としての読み戻し。
方針：共通の境界表示を選び、各面から同じ関手を参照する。
規約：頂点の QCat と元の辺を保持する。
使われ方：四面の指定関手同型の同じ六関手での記述。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：元の三単体の辺 01 を関手として読む。
方針：境界の一単体から通常の射を回収する。
規約：始点 0 と終点 1 の QCat を変更しない。
使われ方：四面の関手同型の両端を同時に揃える。 -/
abbrev catInfinityTetrahedron01 (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋3⦌) :
    s.obj ⟨ULift.up 0⟩ ⟶ s.obj ⟨ULift.up 1⟩ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 2 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 2 s))
/-- 概要：元の三単体の辺 12 を関手として読む。
方針：境界の一単体から通常の射を回収する。
規約：始点 1 と終点 2 の QCat を変更しない。
使われ方：四面の関手同型の両端を同時に揃える。 -/
abbrev catInfinityTetrahedron12 (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋3⦌) :
    s.obj ⟨ULift.up 1⟩ ⟶ s.obj ⟨ULift.up 2⟩ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 2 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 0 s))
/-- 概要：元の三単体の辺 23 を関手として読む。
方針：境界の一単体から通常の射を回収する。
規約：始点 2 と終点 3 の QCat を変更しない。
使われ方：四面の関手同型の両端を同時に揃える。 -/
abbrev catInfinityTetrahedron23 (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋3⦌) :
    s.obj ⟨ULift.up 2⟩ ⟶ s.obj ⟨ULift.up 3⟩ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 0 s))
/-- 概要：元の三単体の辺 02 を関手として読む。
方針：境界の一単体から通常の射を回収する。
規約：始点 0 と終点 2 の QCat を変更しない。
使われ方：四面の関手同型の両端を同時に揃える。 -/
abbrev catInfinityTetrahedron02 (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋3⦌) :
    s.obj ⟨ULift.up 0⟩ ⟶ s.obj ⟨ULift.up 2⟩ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 3 s))
/-- 概要：元の三単体の辺 13 を関手として読む。
方針：境界の一単体から通常の射を回収する。
規約：始点 1 と終点 3 の QCat を変更しない。
使われ方：四面の関手同型の両端を同時に揃える。 -/
abbrev catInfinityTetrahedron13 (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋3⦌) :
    s.obj ⟨ULift.up 1⟩ ⟶ s.obj ⟨ULift.up 3⟩ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 0 s))
/-- 概要：元の三単体の辺 03 を関手として読む。
方針：境界の一単体から通常の射を回収する。
規約：始点 0 と終点 3 の QCat を変更しない。
使われ方：四面の関手同型の両端を同時に揃える。 -/
abbrev catInfinityTetrahedron03 (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋3⦌) :
    s.obj ⟨ULift.up 0⟩ ⟶ s.obj ⟨ULift.up 3⟩ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 2 s))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
