module
public import SerrePositivity.KST.SConstruction.CoherentPathInsertion
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! # 元の豊穣 Path 作用の全パラメータの合成円柱
概要：元の豊穣関手の全 Path 作用を、切断点での実合成に結ぶ円柱を復号する。
方針：切断点挿入と prefix・suffix 分割を同じ豊穣 Hom 作用で評価する。
規約：局所 Kan 性や新しい代表の選択を使わず、合成面を全時刻で固定する。
使われ方：元の K prism の各高次単体から、境界付きの写像空間の族を取り出す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {J : Type u} [LinearOrder J] {a b c : J}
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 切断点を挿入した全 Path を、前半と後半の全パラメータへ分割する。 -/
def coherentPathCutSplit (hab : a ≤ b) (hbc : b ≤ c) :
    nerve (Path a c) ⟶ nerve (Path a b) ⊗ nerve (Path b c) :=
  coherentPathInsertThrough hab hbc ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso a b c).inv

/-- 分割後の元の Path 合成は、同じ切断点挿入を厳密に回収する。 -/
lemma coherentPathCutSplit_comp (hab : a ≤ b) (hbc : b ≤ c) :
    coherentPathCutSplit hab hbc ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap a b c =
      nerveMap (coherentPathInsertFunctor hab hbc) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso_hom_ι, coherentPathCutSplit,
    Category.assoc, Iso.inv_hom_id_assoc, coherentPathInsertThrough_ι]

/-- 挿入された Path の豊穣作用は、元の前半・後半の豊穣作用の実合成。 -/
lemma coherentPathCutSplit_mapping
    (s : EnrichedFunctor SSet.{u} (SimplicialThickening J) C)
    (hab : a ≤ b) (hbc : b ≤ c) :
    nerveMap (coherentPathInsertFunctor hab hbc) ≫ s.map (.mk a) (.mk c) =
      coherentPathCutSplit hab hbc ≫
        (s.map (.mk a) (.mk b) ⊗ₘ s.map (.mk b) (.mk c)) ≫
          eComp SSet (s.obj (.mk a)) (s.obj (.mk b)) (s.obj (.mk c)) := by
  rw [← coherentPathCutSplit_comp, Category.assoc]
  exact congrArg (fun m => coherentPathCutSplit hab hbc ≫ m) (s.map_comp _ _ _)

/-- 全 Path の元の豊穣 Hom の族から、切断点を通る実合成への境界固定円柱。 -/
def coherentPathMappingCutHomotopy
    (s : EnrichedFunctor SSet.{u} (SimplicialThickening J) C)
    (hab : a ≤ b) (hbc : b ≤ c) :
    SSet.Homotopy (s.map (.mk a) (.mk c))
      (coherentPathCutSplit hab hbc ≫
        (s.map (.mk a) (.mk b) ⊗ₘ s.map (.mk b) (.mk c)) ≫
          eComp SSet (s.obj (.mk a)) (s.obj (.mk b)) (s.obj (.mk c))) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (coherentPathInsertionHomotopy hab hbc)
    (s.map (.mk a) (.mk c))
  exact
    { h := H.h
      h₀ := H.h₀
      h₁ := H.h₁.trans (coherentPathCutSplit_mapping s hab hbc)
      rel := H.rel }

/-- 元の合成面にある全族は、復号した円柱の全時刻で厳密に固定する。 -/
lemma coherentPathMappingCutHomotopy_relative
    (s : EnrichedFunctor SSet.{u} (SimplicialThickening J) C)
    (hab : a ≤ b) (hbc : b ≤ c) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := c) b).ι ▷ (Δ[1] : SSet.{u})) ≫
        (coherentPathMappingCutHomotopy s hab hbc).h =
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := c) b : SSet.{u}) Δ[1] ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough b).ι ≫ s.map (.mk a) (.mk c) := by
  change _ ≫ ((coherentPathInsertionHomotopy hab hbc).h ≫ s.map (.mk a) (.mk c)) = _
  rw [← Category.assoc, coherentPathInsertionHomotopy_relative, Category.assoc]

/-- 元の豊穣作用の合成円柱は、全順序写像による前合成と厳密に可換。 -/
lemma coherentPathMappingCutHomotopy_reindex {K : Type u} [LinearOrder K]
    (s : EnrichedFunctor SSet.{u} (SimplicialThickening K) C) (θ : J →o K)
    (hab : a ≤ b) (hbc : b ≤ c) :
    (coherentPathMappingCutHomotopy ((SimplicialThickening.functor θ).comp SSet s)
      hab hbc).h =
    (nerveMap (SimplicialThickening.functorMap θ (.mk a) (.mk c)) ▷
        (Δ[1] : SSet.{u})) ≫
      (coherentPathMappingCutHomotopy s (θ.monotone hab) (θ.monotone hbc)).h := by
  change (coherentPathInsertionHomotopy hab hbc).h ≫
      (nerveMap (SimplicialThickening.functorMap θ (.mk a) (.mk c)) ≫
        s.map (.mk (θ a)) (.mk (θ c))) =
    _ ≫ ((coherentPathInsertionHomotopy (θ.monotone hab) (θ.monotone hbc)).h ≫ _)
  rw [← Category.assoc, ← coherentPathInsertionHomotopy_naturality, Category.assoc]

/-- 円柱の各頂点の元の辺は、同じ Path の包含辺の豊穣作用である。 -/
lemma coherentPathMappingCutHomotopy_vertex
    (s : EnrichedFunctor SSet.{u} (SimplicialThickening J) C)
    (hab : a ≤ b) (hbc : b ≤ c) (p : Path a c) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (coherentPathMappingCutHomotopy s hab hbc)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex p)).edge =
    ((nerve.edgeMk ((coherentPathInsertTransformation hab hbc).app p)).map
      (s.map (.mk a) (.mk c))).edge := by
  exact congrArg ((s.map (.mk a) (.mk c)).app (Opposite.op ⦋1⦌))
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.ordinaryComparisonHomotopy_vertex (coherentPathInsertTransformation hab hbc) p)

/-- 元の端点 Path 上で全パラメータの円柱が返す辺は、指定した元の三角形の辺。 -/
lemma coherentPathMappingCutHomotopy_endpoint_edge
    (s : EnrichedFunctor SSet.{u} (SimplicialThickening J) C)
    (hab : a ≤ b) (hbc : b ≤ c) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (coherentPathMappingCutHomotopy s hab hbc)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentEndpointPath (hab.trans hbc)))).edge =
    ((nerve.edgeMk (coherentEndpointPathToComposite hab hbc)).map
      (s.map (.mk a) (.mk c))).edge := by
  exact congrArg ((s.map (.mk a) (.mk c)).app (Opposite.op ⦋1⦌))
    (coherentPathInsertionHomotopy_endpoint_edge hab hbc)

/-- 同じ元の豊穣単体の表示を変えても、実円柱は依存等号で一致する。 -/
lemma coherentPathMappingCutHomotopy_heq
    {s t : EnrichedFunctor SSet.{u} (SimplicialThickening J) C} (h : s = t)
    (hab : a ≤ b) (hbc : b ≤ c) :
    HEq (coherentPathMappingCutHomotopy s hab hbc).h
      (coherentPathMappingCutHomotopy t hab hbc).h := by
  cases h
  rfl

end SerrePositivity.KST.SConstruction
