module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ColimitSquareComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionComparisonIso

/-! # 同じ span の suspension 比較と余極限頂点比較

概要：同じ span 上の余極限余錐から表示した suspension の標準比較は colimitVertexIso と一致する。
方針：coslice の比較辺を四角形の辺へ送り、始点成分による一意性と終端成分の計算を使う。
規約：同じ span での表示を仮定し、任意の転置にこの条件を自動では付けない。
使われ方：二枝が対称な suspension 模型での交換作用の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：同じ一次単体を持つ二つの辺のホモトピー類は端点込みの Arrow として等しい。
方針：二つの面から端点の等号を回収し、辺の外延性を使う。
規約：値域の quasicategory 性は不要。使われ方：辺の端点表示を揃える操作の比較。 -/
lemma stableHomMk_arrow_of_edge_eq {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x' y') (h : e.edge = f.edge) :
    (Arrow.mk (SSet.Truncated.HomotopyCategory.homMk e) : Arrow (hoFunctor.obj X)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk f) := by
  have hx : x = x' := e.src_eq.symm.trans ((congrArg (fun t => X.δ 1 t) h).trans f.src_eq)
  have hy : y = y' := e.tgt_eq.symm.trans ((congrArg (fun t => X.δ 0 t) h).trans f.tgt_eq)
  subst x'
  subst y'
  have hef : e = f := SSet.Truncated.Edge.ext h
  rw [hef]

/-- 概要：等号による輸送射は端点込みの Arrow として始点の恒等射に等しい。
方針：等号を消す。
規約：任意の圏に適用できる。使われ方：標準比較の始点成分の同定。 -/
lemma stableArrow_eqToHom {C : Type*} [Category* C] {x y : C} (h : x = y) :
    Arrow.mk (eqToHom h) = Arrow.mk (𝟙 x) := by
  subst y
  rfl

/-- 概要：同じ span の普遍余錐として表示された二つの suspension の比較は標準余極限頂点比較。
方針：coslice の標準比較を辺で表し、四角形の始点成分による一意性で標準 suspension 比較と同定する。
規約：四角形表示が一致する二つの余錐を明示する。使われ方：対称な二枝を持つ模型での交換作用。 -/
lemma SuspensionSquare.comparisonIso_eq_colimitVertexIso_arrow
    {X : SSet.{u}} [Quasicategory X] {x : X _⦋0⦌} (s r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x)
    {p : (horn 2 0 : SSet.{u}) ⟶ X} (c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d)
    (hs : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap p).app (Opposite.op ⦋0⦌) c = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square)
    (hr : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap p).app (Opposite.op ⦋0⦌) d = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex r.square) :
    (Arrow.mk (s.comparisonIso r).hom : Arrow (hoFunctor.obj X)) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso c d hc hd).hom := by
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) c d
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso c d hc hd).hom
  let q : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex r.square) := {
    edge := (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap p))).edge
    src_eq := (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap p))).src_eq.trans hs
    tgt_eq := (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap p))).tgt_eq.trans hr }
  have hsource := (stableHomMk_arrow_of_edge_eq
    (q.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0))))
    ((e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap p))).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0)))) rfl).trans
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap_hom_source_arrow p (SSet.Truncated.HomotopyCategory.homMk e))
  have hchosen : Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map
      (s.diagramComparisonIso r).hom) =
      Arrow.mk (𝟙 ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).obj
        (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square)))) := by
    change Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom s.square s.isPushout (r.changeSource s.source_eq.symm))) = _
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_source]
    exact stableArrow_eqToHom _
  have hq : SSet.Truncated.HomotopyCategory.homMk q = (s.diagramComparisonIso r).hom := by
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparison_hom_ext s.square s.isPushout r
    apply Arrow.mk_injective
    have hi := congrArg (fun a : hoFunctor.obj X => Arrow.mk (𝟙 a)) (congrArg Arrow.left hsource)
    exact hsource.trans (hi.symm.trans hchosen.symm)
  have ht := (stableHomMk_arrow_of_edge_eq
    (q.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1))))
    ((e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap p))).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1)))) rfl).trans
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap_hom_target_arrow p (SSet.Truncated.HomotopyCategory.homMk e))
  change Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map
    (SSet.Truncated.HomotopyCategory.homMk q)) =
    Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk e)) at ht
  rw [hq, he] at ht
  exact ht

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
