module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTetrahedronFacePaths
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentPathHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTetrahedronHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTriangleHomotopy

/-!
概要：coherent 三単体の長辺を含む二面の指定辺の同定。
方針：二面の精密化の像を共通の四頂点の path に揃える。
規約：ホモトピー類だけでなく元の一単体を保つ。
使われ方：四面の合成則を指定関手同型の式へ移す。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：面 013 の精密化の像は中間点 1 を加える標準辺。
方針：両端の path を揃え、path の射の一意性を使う。
規約：nerve の一次単体として厳密に一致する。
使われ方：四面の指定辺の共通 Hom への同定。 -/
lemma coherentTetrahedronFace013_chain :
    (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronFace013.{u}).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleRefinement) =
      ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronRefine013 := by
  refine ComposableArrows.ext₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronFace013_short
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronFace013_long ?_
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentPathHom_ext _ _
/-- 概要：面 023 の精密化の像は中間点 2 を加える標準辺。
方針：両端の path を揃え、path の射の一意性を使う。
規約：nerve の一次単体として厳密に一致する。
使われ方：四面の指定辺の共通 Hom への同定。 -/
lemma coherentTetrahedronFace023_chain :
    (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronFace023.{u}).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleRefinement) =
      ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronRefine023 := by
  refine ComposableArrows.ext₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronFace023_short
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronFace023_long ?_
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentPathHom_ext _ _
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
/-- 概要：三単体の面 δ₂ の豊穣辺は中間点 1 を加える辺の像。
方針：面の Hom 写像を展開し、精密化の像の式を使う。
規約：元の一単体の厳密な等式。
使われ方：四面の関手同型の最初の辺の照合。 -/
lemma coherentTetrahedronHom_face_two (s : (SimplicialNerve C) _⦋3⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleHomotopy ((SimplicialNerve C).δ 2 s) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronHomEdge s _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronRefine013).edge := by
  change (s.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩).app (Opposite.op ⦋1⦌)
    ((nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronFace013).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleRefinement)) = _
  rw [coherentTetrahedronFace013_chain]
  rfl
/-- 概要：三単体の面 δ₁ の豊穣辺は中間点 2 を加える辺の像。
方針：面の Hom 写像を展開し、精密化の像の式を使う。
規約：元の一単体の厳密な等式。
使われ方：四面の関手同型の別の最初の辺の照合。 -/
lemma coherentTetrahedronHom_face_one (s : (SimplicialNerve C) _⦋3⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleHomotopy ((SimplicialNerve C).δ 1 s) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronHomEdge s _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronRefine023).edge := by
  change (s.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩).app (Opposite.op ⦋1⦌)
    ((nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronFace023).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleRefinement)) = _
  rw [coherentTetrahedronFace023_chain]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
