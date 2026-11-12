module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.TransportBaseFiber

/-!
概要：基底の辺のホモトピーを coslice の固定終点 fiber 内の比較にする。
方針：恒等終辺を持つ二単体を、点と区間の join 上の図式として読む。
規約：straightening を import する F1 の広い coslice fiber 比較は使わない。
使われ方：Kerodon Remark 7.3.1.10（Tag 02YG） の h での不変性への接続。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：固定始点と終点の coslice fiber の頂点は両端を指定した辺を与える。
方針：点の coslice の辺の終点を fiber 条件で書き換える。
規約：始点は任意の射 a、終点は b。
使われ方：辺のホモトピーを写像空間の辺に変換する。 -/
def cosliceFiberEdge {B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ B) (b : B _⦋0⦌)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) b) _⦋0⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj B) (SSet.yonedaEquiv a) b where
  edge := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge a s.val).edge
  src_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge a s.val).src_eq
  tgt_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge a s.val).tgt_eq.trans
    (s.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero b))

/-- 概要：恒等終辺を持つ二単体は固定終点の coslice fiber の辺を与える。
方針：二単体を Δ[0]⋆Δ[1] に移し、固定図式条件と恒等終辺で fiber へ入れる。
規約：三角形の二つの斜辺が s と t を表す。
使われ方：ホモトピックな基底の辺の輸送の比較。 -/
lemma cosliceFiber_nonempty_edge_of_homotopicL {B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ B) (b : B _⦋0⦌)
    (s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) b) _⦋0⦌)
    (h : SSet.Truncated.HomotopicL (cosliceFiberEdge a b s) (cosliceFiberEdge a b t)) :
    Nonempty (SSet.Truncated.Edge
      (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) b)) s t) := by
  obtain ⟨tri⟩ := h
  have hd₂ : B.δ 2 tri.simplex = (cosliceFiberEdge a b s).edge := tri.d₂
  have hd₁ : B.δ 1 tri.simplex = (cosliceFiberEdge a b t).edge := tri.d₁
  have hd₀ : B.δ 0 tri.simplex = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1 := by
    have hh : B.δ 0 tri.simplex =
        (SSet.Truncated.Edge.id (X := (truncation 2).obj B) b).edge := tri.d₀
    exact hh.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one b).symm
  have hs₀ : B.δ 1 (cosliceFiberEdge a b s).edge = SSet.yonedaEquiv a :=
    (cosliceFiberEdge a b s).src_eq
  let G := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom ≫ SSet.yonedaEquiv.symm tri.simplex
  have hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  have hfixed : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[1] ≫ G = a := by
    dsimp only [G]
    rw [← Category.assoc, hleft, Category.assoc,
      stdSimplex.δ_comp_yonedaEquiv_symm]
    change stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm (B.δ 2 tri.simplex) = a
    rw [hd₂, stdSimplex.δ_comp_yonedaEquiv_symm]
    rw [hs₀, Equiv.symm_apply_apply]
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry G hfixed
  have hg : g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a = SSet.const b := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderCurry_projection]
    dsimp only [G]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_inr, stdSimplex.δ_comp_yonedaEquiv_symm]
    change SSet.yonedaEquiv.symm (B.δ 0 tri.simplex) = SSet.const b
    rw [hd₀]
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    rfl
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) b g hg
  have hf₀ : stdSimplex.δ (1 : Fin 2) ≫ f = SSet.yonedaEquiv.symm s := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, SSet.yonedaEquiv_symm_comp]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective a
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
    dsimp only [G]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_vertex_one, Category.assoc,
      stdSimplex.δ_comp_yonedaEquiv_symm]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (B.δ 2 tri.simplex) = s.val.val
    rw [hd₂]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm
      (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ s.val.val)) = s.val.val
    rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  have hf₁ : stdSimplex.δ (0 : Fin 2) ≫ f = SSet.yonedaEquiv.symm t := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, SSet.yonedaEquiv_symm_comp]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective a
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
    dsimp only [G]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_vertex_one, Category.assoc,
      stdSimplex.δ_comp_yonedaEquiv_symm]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (B.δ 1 tri.simplex) = t.val.val
    rw [hd₁]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm
      (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ t.val.val)) = t.val.val
    rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  refine ⟨{ edge := SSet.yonedaEquiv f, src_eq := ?_, tgt_eq := ?_ }⟩
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) b).δ 1 (SSet.yonedaEquiv f) = s
    rw [← stdSimplex.yonedaEquiv_δ_comp, hf₀, Equiv.apply_symm_apply]
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) b).δ 0 (SSet.yonedaEquiv f) = t
    rw [← stdSimplex.yonedaEquiv_δ_comp, hf₁, Equiv.apply_symm_apply]

/-- 概要：同じホモトピー類の基底の辺は固定終点の coslice fiber 内で同型。
方針：hB の等式を二切断の辺の左ホモトピーへ戻し、fiber の辺と Kan 性を使う。
規約：B は quasicategory。比較するのは同じ始点と終点を持つ辺。
使われ方：指定自然変換の h での等式から輸送の比較への入力。 -/
lemma cosliceFiber_nonempty_iso_of_homMk_eq {B : SSet.{u}} [Quasicategory B]
    (a : (Δ[0] : SSet.{u}) ⟶ B) (b : B _⦋0⦌)
    (s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) b) _⦋0⦌)
    (h : SSet.Truncated.HomotopyCategory.homMk (cosliceFiberEdge a b s) =
      SSet.Truncated.HomotopyCategory.homMk (cosliceFiberEdge a b t)) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso s t) := by
  have h₂ : SSet.Truncated.HomotopyCategory₂.homMk (cosliceFiberEdge a b s) =
      SSet.Truncated.HomotopyCategory₂.homMk (cosliceFiberEdge a b t) := by
    have hh := congrArg (fun m ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((truncation 2).obj B)).map m) h
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory,
      SSet.Truncated.HomotopyCategory.lift_map_homMk] using hh
  have hh : SSet.Truncated.HomotopicL (cosliceFiberEdge a b s)
      (cosliceFiberEdge a b t) := Quotient.exact h₂
  obtain ⟨e⟩ := cosliceFiber_nonempty_edge_of_homotopicL a b s t hh
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalVertexFiber_kanComplex_of_leftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) b
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk e) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) b)) _
  exact ⟨asIso (SSet.Truncated.HomotopyCategory.homMk e)⟩

/-- 概要：基底の辺の h での等式から、輸送先の厳密な fiber 内の同型を得る。
方針：基底の coslice fiber の同型を得て、trivial Kan fibration に沿って持ち上げる。
規約：基底 B は quasicategory、p は cocartesian fibration。
使われ方：右比較錐の指定自然変換のホモトピー不変性の一般部分。 -/
lemma transportBaseFiberTarget_nonempty_iso_of_homMk_eq
    {E B : SSet.{u}} [Quasicategory B]
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration p]
    (b : B _⦋0⦌) (t v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.transportBaseFiber a p b) _⦋0⦌)
    (h : SSet.Truncated.HomotopyCategory.homMk
        (cosliceFiberEdge (a ≫ p) b ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.transportBaseFiberMap a p b).app _ t)) =
      SSet.Truncated.HomotopyCategory.homMk
        (cosliceFiberEdge (a ≫ p) b ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.transportBaseFiberMap a p b).app _ v))) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.transportBaseFiberTarget a p b).app _ t)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.transportBaseFiberTarget a p b).app _ v)) := by
  obtain ⟨e⟩ := cosliceFiber_nonempty_iso_of_homMk_eq (a ≫ p) b _ _ h
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.transportBaseFiberTargetIso a p b t v e⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
