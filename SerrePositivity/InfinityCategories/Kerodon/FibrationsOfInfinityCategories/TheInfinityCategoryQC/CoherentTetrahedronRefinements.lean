module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTetrahedronPaths

/-!
概要：三単体の二通りの精密化と可換正方形。
方針：有限集合の包含を合成し、同じ包含の射として比較する。
規約：両端の頂点を固定する。
使われ方：coherent 三単体の四面の合成則。

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

/-- 概要：直接の path から中間点 1 への精密化。
方針：有限集合の包含を path の圏の射にする。
規約：元の path の端点を固定する。
使われ方：三単体の二通りの精密化の指定辺。 -/
def coherentTetrahedronRefine013 : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath03.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath013.{u} :=
  ⟨⟨⟨by
    intro k hk
    change k = ULift.up 0 ∨ k = ULift.up 3 at hk
    rcases hk with rfl | rfl <;> simp [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath013, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentFourPath]⟩⟩⟩
/-- 概要：直接の path から中間点 2 への精密化。
方針：有限集合の包含を path の圏の射にする。
規約：元の path の端点を固定する。
使われ方：三単体の二通りの精密化の指定辺。 -/
def coherentTetrahedronRefine023 : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath03.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath023.{u} :=
  ⟨⟨⟨by
    intro k hk
    change k = ULift.up 0 ∨ k = ULift.up 3 at hk
    rcases hk with rfl | rfl <;> simp [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath023, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentFourPath]⟩⟩⟩
/-- 概要：中間点 1 の path から全頂点への精密化。
方針：有限集合の包含を path の圏の射にする。
規約：元の path の端点を固定する。
使われ方：三単体の二通りの精密化の指定辺。 -/
def coherentTetrahedronRefine013Full :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath013.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath0123.{u} := ⟨⟨⟨by intro k hk; trivial⟩⟩⟩
/-- 概要：中間点 2 の path から全頂点への精密化。
方針：有限集合の包含を path の圏の射にする。
規約：元の path の端点を固定する。
使われ方：三単体の二通りの精密化の指定辺。 -/
def coherentTetrahedronRefine023Full :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath023.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTetrahedronPath0123.{u} := ⟨⟨⟨by intro k hk; trivial⟩⟩⟩
/-- 概要：中間点を異なる順序で加えた二つの精密化は一致する。
方針：path の射の包含の証明の無関係性を使う。
規約：直接の path から全頂点の path への厳密な射の等式。
使われ方：豊穣 Hom 内の四面の合成則の根拠。 -/
lemma coherentTetrahedronRefinement_square :
    coherentTetrahedronRefine013.{u} ≫ coherentTetrahedronRefine013Full =
      coherentTetrahedronRefine023 ≫ coherentTetrahedronRefine023Full := by rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
