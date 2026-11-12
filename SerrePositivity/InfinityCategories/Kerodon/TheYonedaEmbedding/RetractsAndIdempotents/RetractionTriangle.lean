module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakShape
public import SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.RetractClosure
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元のホモトピー圏内の retract を、同じ二頂点の実際の分裂三角形へ戻す。
方針：元の二射の類を一本の辺で表し、同じ恒等辺を持つ合成二単体を回収する。
規約：全 coherent 分裂への延長はまだ仮定しない。
使われ方：HTT 4.4.5 の弱い retract 図式の存在の入口。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 同じ二頂点の元の二射と、同じ恒等長辺を持つ実際の合成三角形。 -/
@[kerodon 03YZ]
abbrev RetractionTriangle {X : SSet.{u}} (x y : X _⦋0⦌) :=
  Σ i : SSet.Edge y x, Σ r : SSet.Edge x y, SSet.Edge.CompStruct i r (SSet.Edge.id y)

/-- 元の分裂三角形は、元の二辺の射の類を持つ同じ二頂点の retract を与える。 -/
def RetractionTriangle.vertexRetraction {X : SSet.{u}} {x y : X _⦋0⦌}
    (t : RetractionTriangle x y) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction y x where
  i := HomotopyCategory.homMk t.1
  r := HomotopyCategory.homMk t.2.1
  retract := (HomotopyCategory.homMk_comp_homMk t.2.2).trans (HomotopyCategory.homMk_id y)

/-- 元の retract の二射の類を同じまま保つ、実際の分裂三角形が存在する。 -/
lemma VertexRetraction.triangle_exists {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction y x) :
    ∃ t : RetractionTriangle x y,
      HomotopyCategory.homMk t.1 = s.i ∧ HomotopyCategory.homMk t.2.1 = s.r := by
  obtain ⟨i, hi⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective y x s.i
  obtain ⟨r, hr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y s.r
  have h : SSet.Truncated.HomotopyCategory.homMk i ≫
      SSet.Truncated.HomotopyCategory.homMk r =
        SSet.Truncated.HomotopyCategory.homMk
          (SSet.Truncated.Edge.id (X := (truncation 2).obj X) y) := by
    rw [hi, hr, s.retract, SSet.Truncated.HomotopyCategory.homMk_id]
    rfl
  obtain ⟨h⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac h
  let T : RetractionTriangle x y := ⟨SSet.Edge.ofTruncated i,
    SSet.Edge.ofTruncated r, SSet.Edge.CompStruct.ofTruncated h⟩
  exact ⟨T, hi, hr⟩

/-- 元の分裂三角形の同じ二単体全体。 -/
def RetractionTriangle.diagram {X : SSet.{u}} {x y : X _⦋0⦌}
    (t : RetractionTriangle x y) : (Δ[2] : SSet.{u}) ⟶ X :=
  SSet.yonedaEquiv.symm t.2.2.simplex

/-- 元の分裂三角形の長辺は、元の同じ分裂点への退化辺。 -/
lemma RetractionTriangle.diagram_longEdge {X : SSet.{u}} {x y : X _⦋0⦌}
    (t : RetractionTriangle x y) :
    stdSimplex.δ (1 : Fin 3) ≫ t.diagram = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.longEdgeCollapse ≫ SSet.yonedaEquiv.symm y := by
  have h := t.2.2.δ_one_yonedaEquiv_symm
  change _ = SSet.yonedaEquiv.symm (X.σ (0 : Fin 1) y) at h
  rw [← stdSimplex.σ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_zero, SSet.comp_const] at h
  rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const]
  exact h

/-- 元の分裂三角形を、同じ二単体と同じ頂点を保って元の Ret の商へ降ろす。 -/
def RetractionTriangle.weakDiagram {X : SSet.{u}} {x y : X _⦋0⦌}
    (t : RetractionTriangle x y) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakRetractionDiagram X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDesc t.diagram (SSet.yonedaEquiv.symm y) t.diagram_longEdge

/-- 元の Ret 図式の三角形への制限は、元の同じ分裂三角形そのもの。 -/
lemma RetractionTriangle.weakDiagram_triangle {X : SSet.{u}} {x y : X _⦋0⦌}
    (t : RetractionTriangle x y) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle ≫ t.weakDiagram = t.diagram :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDesc_triangle _ _ _

/-- 元の Ret 図式の分裂点への制限は、元の同じ分裂頂点そのもの。 -/
lemma RetractionTriangle.weakDiagram_imagePoint {X : SSet.{u}} {x y : X _⦋0⦌}
    (t : RetractionTriangle x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakImagePoint ≫ t.weakDiagram = SSet.yonedaEquiv.symm y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDesc_imagePoint _ _ _

/-- 元の Ret 図式への降下は、元の包含の辺を厳密に保持する。 -/
lemma RetractionTriangle.weakDiagram_section {X : SSet.{u}} {x y : X _⦋0⦌}
    (t : RetractionTriangle x y) :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle ≫ t.weakDiagram =
      SSet.yonedaEquiv.symm t.1.edge := by
  rw [t.weakDiagram_triangle]
  exact t.2.2.δ_two_yonedaEquiv_symm

/-- 元の Ret 図式への降下は、元の射影の辺を厳密に保持する。 -/
lemma RetractionTriangle.weakDiagram_retraction {X : SSet.{u}} {x y : X _⦋0⦌}
    (t : RetractionTriangle x y) :
    stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle ≫ t.weakDiagram =
      SSet.yonedaEquiv.symm t.2.1.edge := by
  rw [t.weakDiagram_triangle]
  exact t.2.2.δ_zero_yonedaEquiv_symm

/-- 元の頂点の retract 条件は、同じ二頂点の実際の分裂三角形の存在と同値。 -/
@[kerodon 03YZ]
lemma isVertexRetractOf_iff_retractionTriangle {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf y x ↔ Nonempty (RetractionTriangle x y) := by
  constructor
  · rintro ⟨s⟩
    obtain ⟨t, _, _⟩ := s.triangle_exists
    exact ⟨t⟩
  · rintro ⟨t⟩
    exact ⟨t.vertexRetraction⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
