module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningEdgeAction

/-!
概要：指定された頂点の fiber 同型を使って straightening の辺を比較する。
方針：射の圏で端点の等式による移送を消し、始点と終点の制限の式を結ぶ。
規約：既存の evaluateIso と transport の一単体を保持する。
使われ方：一般の底上の straightening の transport 比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：射の圏で等しい合成可能な二組の射の合成も等しい。
方針：端点の等式を消去して通常の合成の合同性へ戻す。
規約：二組の端点の型は最初から一致しなくてよい。
使われ方：端点表示を変えた比較の正方形の合成。 -/
lemma arrowMk_comp_congr {C : Type u} [Category.{v} C]
    {a b c a' b' c' : C} (f : a ⟶ b) (g : b ⟶ c)
    (f' : a' ⟶ b') (g' : b' ⟶ c')
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨ha, hb, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp hf
  obtain ⟨_, hc, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hg
  subst a' b' c'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  rw [hf, hg]

/-- 概要：一単体の始点での fiber 比較は、指定済みの頂点評価の同型を表す。
方針：始点への制限の辺が退化であることを使い、端点の移送を消去する。
規約：元の evaluateIso を使う。
使われ方：終点の transport 比較で始点の同型を揃える。 -/
lemma leftStraighteningInfinityMap_firstVertexFiberIso_arrow {B : SSet.{u}}
    (σ : B _⦋1⦌) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_firstVertexFiberIso σ).hom =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_evaluateIso
        (B.map (SimplexCategory.δ (1 : Fin 2)).op σ)).hom := by
  have h := congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_initialRestriction_fiberIso σ)
  rw [← Category.assoc, Arrow.arrow_mk_comp_eqToHom] at h
  have he := SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_simplexRestrictionEdge
      (SimplexCategory.δ (1 : Fin 2)) σ).toTruncated
    (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (ULift.up (B.map (SimplexCategory.δ (1 : Fin 2)).op σ))))).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_initialRestriction_edge σ)
  simp only [SSet.Edge.toTruncated_id, SSet.Truncated.HomotopyCategory.homMk_id] at he
  calc
    _ = _ := h.symm
    _ = _ := arrowMk_comp_congr _ _ _ _ he
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_evaluateIso_arrow _).symm
    _ = _ := by rw [Category.id_comp]

/-- 概要：底の一単体の Yoneda 表示の始点は元の始点。
方針：零頂点の作用素を初面と同定する。
規約：元の底の実際の零単体の等式。
使われ方：既存 transport の端点を底の辺の端点へ揃える。 -/
lemma yonedaEdge_firstVertex {B : SSet.{u}} (σ : B _⦋1⦌) :
    (SSet.yonedaEquiv.symm σ).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      B.map (SimplexCategory.δ (1 : Fin 2)).op σ := by
  change B.map (stdSimplex.obj₀Equiv.symm (0 : Fin 2)).down.op σ = _
  have h : (stdSimplex.obj₀Equiv.symm (0 : Fin 2)).down =
      SimplexCategory.δ (1 : Fin 2) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    fin_cases k
    rfl
  exact congrArg (fun α : ⦋0⦌ ⟶ ⦋1⦌ ↦ B.map α.op σ) h

/-- 概要：底の一単体の Yoneda 表示の終点は元の終点。
方針：一頂点の作用素を終面と同定する。
規約：元の底の実際の零単体の等式。
使われ方：既存 transport の終点の同定。 -/
lemma yonedaEdge_lastVertex {B : SSet.{u}} (σ : B _⦋1⦌) :
    (SSet.yonedaEquiv.symm σ).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      B.map (SimplexCategory.δ (0 : Fin 2)).op σ := by
  change B.map (stdSimplex.obj₀Equiv.symm (1 : Fin 2)).down.op σ = _
  have h : (stdSimplex.obj₀Equiv.symm (1 : Fin 2)).down =
      SimplexCategory.δ (0 : Fin 2) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    fin_cases k
    rfl
  exact congrArg (fun α : ⦋0⦌ ⟶ ⦋1⦌ ↦ B.map α.op σ) h

/-- 概要：既存 transport を元の底の辺の端点を持つ形で表示する。
方針：Yoneda 表示の両端の等式で辺の端点だけを揃える。
規約：transport の一単体そのものは変更しない。
使われ方：指定済み evaluateIso の両端との合成。 -/
def leftFibrationNaturalTransportSimplexEdge {B : SSet.{u}} (σ : B _⦋1⦌) :
    SSet.Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation
        (B.map (SimplexCategory.δ (1 : Fin 2)).op σ)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation
        (B.map (SimplexCategory.δ (0 : Fin 2)).op σ))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (SSet.yonedaEquiv.symm σ)).ofEq
    (congrArg (fun b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation b))
      (yonedaEdge_firstVertex σ))
    (congrArg (fun b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation b))
      (yonedaEdge_lastVertex σ))

/-- 辺の端点だけの輸送は、ホモトピー圏の射の圏で同じ射を表す。 -/
lemma arrow_homMk_edge_ofEq {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (e : SSet.Edge x y) (hx : x = x') (hy : y = y') :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (e.ofEq hx hy).toTruncated) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homMk_edge_ofEq]
  simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom, Arrow.arrow_mk_eqToHom_comp]

private lemma transport_simplex_arrow {B : SSet.{u}} (σ : B _⦋1⦌) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (SSet.yonedaEquiv.symm σ)).toTruncated) =
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (leftFibrationNaturalTransportSimplexEdge σ).toTruncated) :=
  (arrow_homMk_edge_ofEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (SSet.yonedaEquiv.symm σ))
    (congrArg (fun b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation b))
      (yonedaEdge_firstVertex σ))
    (congrArg (fun b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation b))
      (yonedaEdge_lastVertex σ))).symm

private lemma terminal_transport_arrow {B : SSet.{u}} (σ : B _⦋1⦌) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_simplexRestrictionEdge
        (SimplexCategory.δ (0 : Fin 2)) σ).toTruncated ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_firstVertexFiberIso
        (B.map (SimplexCategory.δ (0 : Fin 2)).op σ)).hom) =
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_firstVertexFiberIso σ).hom ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (SSet.yonedaEquiv.symm σ)).toTruncated) := by
  have h := congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_terminalRestriction_transport σ)
  rw [← Category.assoc, Arrow.arrow_mk_comp_eqToHom] at h
  exact h

private lemma terminal_evaluate_arrow {B : SSet.{u}} (σ : B _⦋1⦌) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_simplexRestrictionEdge
        (SimplexCategory.δ (0 : Fin 2)) σ).toTruncated ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_firstVertexFiberIso
        (B.map (SimplexCategory.δ (0 : Fin 2)).op σ)).hom) =
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_edge (SSet.Edge.mk σ rfl rfl)).toTruncated ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_evaluateIso
        (B.map (SimplexCategory.δ (0 : Fin 2)).op σ)).hom) := by
  apply arrowMk_comp_congr
  · exact SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_simplexRestrictionEdge
        (SimplexCategory.δ (0 : Fin 2)) σ).toTruncated
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_edge (SSet.Edge.mk σ rfl rfl)).toTruncated
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_terminalRestriction_edge σ)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_evaluateIso_arrow _).symm

private lemma source_transport_arrow {B : SSet.{u}} (σ : B _⦋1⦌) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_firstVertexFiberIso σ).hom ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (SSet.yonedaEquiv.symm σ)).toTruncated) =
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_evaluateIso
        (B.map (SimplexCategory.δ (1 : Fin 2)).op σ)).hom ≫
      SSet.Truncated.HomotopyCategory.homMk
        (leftFibrationNaturalTransportSimplexEdge σ).toTruncated) := by
  apply arrowMk_comp_congr
  · exact leftStraighteningInfinityMap_firstVertexFiberIso_arrow σ
  · exact transport_simplex_arrow σ

/-- 概要：straightening の実際の辺は、両端の指定評価同型で既存 transport と可換。
方針：終点の比較を始点の退化辺の比較へ接続し、端点の移送を射の圏で消す。
規約：evaluateIso と transport の既存の一単体を使用する。
使われ方：一般の底の straightening と相対表現の全パラメーターの比較。 -/
lemma leftStraighteningInfinityMap_edge_evaluateIso_arrow {B : SSet.{u}} (σ : B _⦋1⦌) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_edge (SSet.Edge.mk σ rfl rfl)).toTruncated ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_evaluateIso
        (B.map (SimplexCategory.δ (0 : Fin 2)).op σ)).hom) =
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_evaluateIso
        (B.map (SimplexCategory.δ (1 : Fin 2)).op σ)).hom ≫
      SSet.Truncated.HomotopyCategory.homMk
        (leftFibrationNaturalTransportSimplexEdge σ).toTruncated) :=
  (terminal_evaluate_arrow σ).symm.trans
    ((terminal_transport_arrow σ).trans (source_transport_arrow σ))

/-- 両端の指定済みの fiber 評価同型は、straightening の実際の辺と transport を結ぶ。 -/
lemma leftStraighteningInfinityMap_edge_evaluateIso {B : SSet.{u}} (σ : B _⦋1⦌) :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_edge (SSet.Edge.mk σ rfl rfl)).toTruncated ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_evaluateIso
        (B.map (SimplexCategory.δ (0 : Fin 2)).op σ)).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_evaluateIso
        (B.map (SimplexCategory.δ (1 : Fin 2)).op σ)).hom ≫
      SSet.Truncated.HomotopyCategory.homMk
        (leftFibrationNaturalTransportSimplexEdge σ).toTruncated := by
  obtain ⟨_, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp
    (leftStraighteningInfinityMap_edge_evaluateIso_arrow σ)
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- straightening の辺の射は、指定された両端の同型による既存 transport の共役。 -/
lemma leftStraighteningInfinityMap_edge_hom {B : SSet.{u}} (σ : B _⦋1⦌) :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_edge (SSet.Edge.mk σ rfl rfl)).toTruncated =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_evaluateIso
        (B.map (SimplexCategory.δ (1 : Fin 2)).op σ)).hom ≫
      SSet.Truncated.HomotopyCategory.homMk
        (leftFibrationNaturalTransportSimplexEdge σ).toTruncated ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_evaluateIso
        (B.map (SimplexCategory.δ (0 : Fin 2)).op σ)).inv := by
  have h := congrArg (fun f ↦ f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_evaluateIso
    (B.map (SimplexCategory.δ (0 : Fin 2)).op σ)).inv)
    (leftStraighteningInfinityMap_edge_evaluateIso σ)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
