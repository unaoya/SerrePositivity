module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EdgeClosedEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TruncatedTriangles
public import SerrePositivity.DifferentialGraded.Category.Basic

/-!
辺の左右のホモトピーと閉零射の境界関係の比較。HA Example 1.3.1.8。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels

open CategoryTheory Opposite DifferentialGraded
open CategoryTheory.SimplicialObject.Truncated
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：端点付きの辺は既存の閉零圏の射を定める。
方針：閉零元を単位複体からの射へ戻す既存の同値を使う。
規約：HA Example 1.3.1.8。使われ方：H⁰ への比較関手の射写像の代表元。 -/
def edgeClosed {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂} (e : SSet.Truncated.Edge x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.vertexClosed x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.vertexClosed y := (closedHomEquiv A D _ _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle e)

/-- 概要：辺から作った閉零射の評価は、その辺の閉零成分に戻る。
方針：既存の同値の右逆則を使う。
規約：HA Example 1.3.1.8。使われ方：境界関係の成分による判定。 -/
lemma edgeClosed_cycle {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂} (e : SSet.Truncated.Edge x y) :
    closedHomEquiv A D _ _ (edgeClosed e) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle e :=
  (closedHomEquiv A D _ _).apply_symm_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle e)

/-- 概要：両端の対象を等式で移送した閉零元の値は、元の値と異種等号で一致する。
方針：対象の等式を消去して反射律に帰着する。
規約：HA Example 1.3.1.8。使われ方：端点の移送と退化辺の成分の比較。 -/
lemma castCycle_val_heq {x y x' y' : D} (hx : x = x') (hy : y = y')
    (f : zeroCycles (homObject A D x y)) :
    HEq ((cast (by rw [hx, hy]) f : zeroCycles (homObject A D x' y')).val) f.val := by
  subst hx
  subst hy
  rfl

/-- 概要：端点へ移送した辺の閉零元の値は、元の一単体の値と異種等号で一致する。
方針：閉零元の対象の移送の異種等号を適用する。
規約：HA Example 1.3.1.8。使われ方：面と退化の成分計算との接続。 -/
lemma edgeCycle_val_heq {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂} (e : SSet.Truncated.Edge x y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle e).val (e.edge.edgeCycle 0 1 (by decide)).val :=
  castCycle_val_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_source_obj e) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_target_obj e) _

/-- 概要：退化した恒等辺の閉零成分は dg 単位。
方針：二点を潰す退化写像の成分の単位分岐を評価する。
規約：HA Construction 1.3.1.6。使われ方：左右の辺ホモトピーを境界へ翻訳する。 -/
lemma edgeCycle_id (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle (SSet.Truncated.Edge.id x) = unitElement A (x.obj 0) := by
  apply Subtype.ext
  apply eq_of_heq
  refine (edgeCycle_val_heq (SSet.Truncated.Edge.id x)).trans ?_
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.σ_hom_of_collapsed_pair A D 0 x {0, 1} 0 1 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 概要：左辺ホモトピーは二つの閉零成分の差が境界であることと同値。
方針：合成構造の原始元による特徴づけと dg 単位則を使う。
規約：Kerodon §2.5.3（Tag 00PK）、HA Example 1.3.1.8。使われ方：左ホモトピー類による商の比較。 -/
lemma homotopicL_iff_exists {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂}
    (f g : SSet.Truncated.Edge x y) :
    SSet.Truncated.HomotopicL f g ↔ ∃ t : GradedHom A (x.obj 0) (y.obj 0) (-1),
      (homObject A D (x.obj 0) (y.obj 0)).d (-1) 0 t = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle f).val - (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle g).val := by
  change Nonempty (SSet.Truncated.Edge.CompStruct f (SSet.Truncated.Edge.id y) g) ↔ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compStruct_iff_homotopy, edgeCycle_id]
  simp only [unit_compose]
  rfl

/-- 概要：右辺ホモトピーは二つの閉零成分の差が境界であることと同値。
方針：合成構造の原始元による特徴づけと dg 単位則を使う。
規約：Kerodon §2.5.3（Tag 00PK）、HA Example 1.3.1.8。使われ方：右ホモトピーと境界関係の比較。 -/
lemma homotopicR_iff_exists {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂}
    (f g : SSet.Truncated.Edge x y) :
    SSet.Truncated.HomotopicR f g ↔ ∃ t : GradedHom A (x.obj 0) (y.obj 0) (-1),
      (homObject A D (x.obj 0) (y.obj 0)).d (-1) 0 t = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle f).val - (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle g).val := by
  change Nonempty (SSet.Truncated.Edge.CompStruct (SSet.Truncated.Edge.id x) f g) ↔ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compStruct_iff_homotopy, edgeCycle_id]
  simp only [compose_unit]
  rfl

/-- 概要：辺を閉零射にしたときの境界関係は、その閉零成分の差の原始元の存在に一致する。
方針：既存の H⁰ の射の等式の境界判定と、閉零射の評価の逆則を使う。
規約：HA Example 1.3.1.8。使われ方：Mathlib の辺ホモトピーと既存の境界関係の接続。 -/
lemma boundary_iff_exists {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂}
    (f g : SSet.Truncated.Edge x y) :
    boundaryRelation A D (edgeClosed f) (edgeClosed g) ↔
      ∃ t : GradedHom A (x.obj 0) (y.obj 0) (-1),
        (homObject A D (x.obj 0) (y.obj 0)).d (-1) 0 t = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle f).val - (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle g).val := by
  rw [← toHomotopy_map_eq_iff A D, toHomotopy_map_eq_iff_boundary A D]
  change (∃ t : GradedHom A (x.obj 0) (y.obj 0) (-1),
      (homObject A D (x.obj 0) (y.obj 0)).d (-1) 0 t =
        (closedHomEquiv A D _ _ (edgeClosed f)).val -
        (closedHomEquiv A D _ _ (edgeClosed g)).val) ↔ _
  rw [edgeClosed_cycle, edgeClosed_cycle]

/-- 概要：左辺ホモトピーは既存の閉零圏の境界関係と同値。
方針：両方を閉零成分の差の原始元の存在で特徴づける。
規約：Kerodon §2.5.3（Tag 00PK）、HA Example 1.3.1.8。使われ方：二つのホモトピー圏の射の同値。 -/
lemma homotopicL_iff_boundary {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂}
    (f g : SSet.Truncated.Edge x y) :
    SSet.Truncated.HomotopicL f g ↔ boundaryRelation A D (edgeClosed f) (edgeClosed g) :=
  (homotopicL_iff_exists f g).trans (boundary_iff_exists f g).symm

/-- 概要：右辺ホモトピーは既存の閉零圏の境界関係と同値。
方針：両方を閉零成分の差の原始元の存在で特徴づける。
規約：Kerodon §2.5.3（Tag 00PK）、HA Example 1.3.1.8。使われ方：左右どちらの辺ホモトピーでも H⁰ を得る。 -/
lemma homotopicR_iff_boundary {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂}
    (f g : SSet.Truncated.Edge x y) :
    SSet.Truncated.HomotopicR f g ↔ boundaryRelation A D (edgeClosed f) (edgeClosed g) :=
  (homotopicR_iff_exists f g).trans (boundary_iff_exists f g).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels
