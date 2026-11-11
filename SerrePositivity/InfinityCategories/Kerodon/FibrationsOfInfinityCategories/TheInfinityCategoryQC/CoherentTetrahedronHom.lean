module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTetrahedronRefinements
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans

/-!
概要：coherent 三単体の四つの精密化の豊穣 Hom 内の可換正方形。
方針：同じ両端の Hom の写像で path の圏の四角形を送る。
規約：対象と Hom の宇宙を分ける。
使われ方：指定された四面の関手同型の合成則。

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

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 概要：三単体の同じ両端間の path の精密化を豊穣 Hom の辺にする。
方針：精密化の nerve の辺を三単体の Hom の写像で送る。
規約：両端は頂点 0 と 3 の間の同じ豊穣 Hom の中にある。
使われ方：四面の可換性を同じ関手空間で比較する。 -/
def coherentTetrahedronHomEdge (s : (SimplicialNerve C) _⦋3⦌)
    {P Q : SimplicialThickening.Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3)}
    (r : P ⟶ Q) :
    (SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 3⟩)).Edge
      ((s.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ P))
      ((s.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ Q)) :=
  (nerve.edgeMk r).map (s.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩)
/-- 概要：三単体による精密化の像はホモトピー圏内で合成を保つ。
方針：通常の合成の nerve の三角形を豊穣 Hom へ送る。
規約：標的の局所 Kan 性は不要。
使われ方：二通りの精密化の合成を比較する。 -/
lemma coherentTetrahedronHomEdge_comp (s : (SimplicialNerve C) _⦋3⦌)
    {P Q R : SimplicialThickening.Path
      (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3)} (r : P ⟶ Q) (t : Q ⟶ R) :
    SSet.Truncated.HomotopyCategory.homMk (coherentTetrahedronHomEdge s r).toTruncated ≫
        SSet.Truncated.HomotopyCategory.homMk (coherentTetrahedronHomEdge s t).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (coherentTetrahedronHomEdge s (r ≫ t)).toTruncated :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    ((show SSet.Edge.CompStruct (nerve.edgeMk r) (nerve.edgeMk t) (nerve.edgeMk (r ≫ t)) from
      SSet.Edge.CompStruct.mk (ComposableArrows.mk₂ r t)
        (nerve.δ₂_mk₂_eq r t) (nerve.δ₀_mk₂_eq r t) (nerve.δ₁_mk₂_eq r t)).map
          (s.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩)).toTruncated
/-- 概要：三単体の二通りの精密化の像は豊穣 Hom のホモトピー圏で可換。
方針：精密化の厳密な正方形と合成の保存を使う。
規約：四つの指定された辺の類の合成の等式。
使われ方：四面から読み戻す関手同型の合成則。 -/
lemma coherentTetrahedronHom_square (s : (SimplicialNerve C) _⦋3⦌) :
    SSet.Truncated.HomotopyCategory.homMk
        (coherentTetrahedronHomEdge s _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronRefine013).toTruncated ≫
      SSet.Truncated.HomotopyCategory.homMk
        (coherentTetrahedronHomEdge s _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronRefine013Full).toTruncated =
    SSet.Truncated.HomotopyCategory.homMk
        (coherentTetrahedronHomEdge s _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronRefine023).toTruncated ≫
      SSet.Truncated.HomotopyCategory.homMk
        (coherentTetrahedronHomEdge s _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronRefine023Full).toTruncated := by
  exact (coherentTetrahedronHomEdge_comp s _ _).trans
    ((congrArg (fun r ↦ SSet.Truncated.HomotopyCategory.homMk
      (coherentTetrahedronHomEdge s r).toTruncated) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronRefinement_square).trans
      (coherentTetrahedronHomEdge_comp s _ _).symm)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
