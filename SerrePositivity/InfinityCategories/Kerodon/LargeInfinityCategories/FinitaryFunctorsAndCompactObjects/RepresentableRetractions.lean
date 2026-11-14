module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.ColimitRetractions
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletenessOpposite
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge

/-!
概要：元の対象の retract は、元の全共変表現可能関手の自然 retract を与える。
方針：反対圏の Yoneda を二重反転への前合成で全関手圏へ写す。
規約：全単体を持つ一つの共変 Hom 関手を使用。値ごとの同値だけで代用しない。
使われ方：κ-compact 対象の retract 閉性。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects


/-- 同じ実際の分裂三角形を持ち上げると、同じ二頂点の retract が得られる。 -/
lemma isVertexRetractOf_ulift {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf (X := (SSet.uliftFunctor.{v, u}).obj X) (ULift.up x) (ULift.up y) := by
  obtain ⟨t, _hi, _hr⟩ := h.some.triangle_exists
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedCompStruct.{u, v} t.2.2.toTruncated
  change SSet.Truncated.Edge.CompStruct _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x)) at ht
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge_id] at ht
  let T : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractionTriangle (X := (SSet.uliftFunctor.{v, u}).obj X)
      (ULift.up y) (ULift.up x) :=
    ⟨SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} t.1.toTruncated),
      SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} t.2.1.toTruncated),
      SSet.Edge.CompStruct.ofTruncated ht⟩
  exact ⟨T.vertexRetraction⟩

/-- 元の反対圏から、全共変表現可能関手の ∞ 圏への一つの単体的関手。 -/
def covariantRepresentableDiagram (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C.op ≫
    (pre ((SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctorCompOpFunctorIso.app C).inv)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}

/-- 同じ全関手の値は、定義に使用した元の共変表現可能関手そのもの。 -/
lemma covariantRepresentableDiagram_vertex {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :
    (covariantRepresentableDiagram C).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm x)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x) := by
  dsimp only [covariantRepresentableDiagram]
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_vertex]
  rfl

/-- 元の対象の retract は、同じ元の全 Hom 関手の自然 retract を与える。 -/
lemma covariantRepresentable_retract {C : SSet.{u}} [Quasicategory C] {x y : C _⦋0⦌}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity y)) := by
  have hr := (isVertexRetractOf_ulift.{u, u + 1} h.op).map (covariantRepresentableDiagram C)
  rwa [covariantRepresentableDiagram_vertex, covariantRepresentableDiagram_vertex] at hr

/-- κ-compact 対象の元のホモトピー圏内の retract も κ-compact。 -/
lemma IsKappaCompact.of_retract {κ : Cardinal.{u}} {C : SSet.{max u v}} [Quasicategory C]
    {x y : C _⦋0⦌} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x y) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PreservesKappaFilteredColimits.of_retract (covariantRepresentable_retract h).some hy

/-- 元の頂点同型は、小さい添字についての κ-compact 性を保ち反映する。 -/
lemma isKappaCompact_iff_of_iso {κ : Cardinal.{u}} {C : SSet.{max u v}} [Quasicategory C]
    {x y : C _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ x ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ y :=
  ⟨IsKappaCompact.of_retract (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.of_iso e.symm),
    IsKappaCompact.of_retract (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.of_iso e)⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.1.6.4"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentable_retract
attribute [cite HTT "5.1.6.8" (partial := component) "仮定：指定前層が元の米田像の retract（Lean が強い：S は準圏）。結論：同じ全共変 Hom は、準圏を形状とする任意の小余極限を保存する。米田評価と指定宇宙変更の同型、および retract の余極限判定で得る（(2) からの保存のうち準圏形状の部分に一致。任意の単体集合形状と (1)⇒(2) は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentable_retract
attribute [cite HTT "5.3.4.16"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.of_retract
attribute [cite HTT "5.3.4.17" (partial := special) "仮定：正則 κ、小準圏 C と表現可能前層の有限形状余極限の retract X（Lean が強い：κ-small 形状を有限形状に限定）。結論：同じ X が κ-compact（この場合の (1)⇒(2) と一致）。各表現可能頂点、同じ指定余極限、その retract の三宣言を直接適用する。逆方向と一般 κ-small 形状の表示は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.of_retract
