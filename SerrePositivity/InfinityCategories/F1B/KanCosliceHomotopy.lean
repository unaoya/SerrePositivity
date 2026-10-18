module

public import SerrePositivity.InfinityCategories.F1B.KanTransportBaseFiber

/-!
概要：基底の辺のホモトピーを coslice の固定終点 fiber 内の比較にする。
方針：恒等終辺を持つ二単体を、点と区間の join 上の図式として読む。
規約：straightening を import する F1 の広い coslice fiber 比較は使わない。
使われ方：Kerodon Remark 7.3.1.10 の h での不変性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：固定始点と終点の coslice fiber の頂点は両端を指定した辺を与える。
方針：点の coslice の辺の終点を fiber 条件で書き換える。
規約：始点は任意の射 a、終点は b。
使われ方：辺のホモトピーを写像空間の辺に変換する。 -/
def kanCosliceFiberEdge {B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ B) (b : B _⦋0⦌)
    (s : (vertexFiber (sliceUnderProjection a) b) _⦋0⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj B) (SSet.yonedaEquiv a) b where
  edge := (pointCosliceVertexEdge a s.val).edge
  src_eq := (pointCosliceVertexEdge a s.val).src_eq
  tgt_eq := (pointCosliceVertexEdge a s.val).tgt_eq.trans
    (s.property.trans (pinchedConstant_zero b))

/-- 概要：恒等終辺を持つ二単体は固定終点の coslice fiber の辺を与える。
方針：二単体を Δ[0]⋆Δ[1] に移し、固定図式条件と恒等終辺で fiber へ入れる。
規約：三角形の二つの斜辺が s と t を表す。
使われ方：ホモトピックな基底の辺の輸送の比較。 -/
lemma kanCosliceFiber_nonempty_edge_of_homotopicL {B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ B) (b : B _⦋0⦌)
    (s t : (vertexFiber (sliceUnderProjection a) b) _⦋0⦌)
    (h : SSet.Truncated.HomotopicL (kanCosliceFiberEdge a b s) (kanCosliceFiberEdge a b t)) :
    Nonempty (SSet.Truncated.Edge
      (X := (truncation 2).obj (vertexFiber (sliceUnderProjection a) b)) s t) := by
  obtain ⟨tri⟩ := h
  have hd₂ : B.δ 2 tri.simplex = (kanCosliceFiberEdge a b s).edge := tri.d₂
  have hd₁ : B.δ 1 tri.simplex = (kanCosliceFiberEdge a b t).edge := tri.d₁
  have hd₀ : B.δ 0 tri.simplex = PinchedHom.constant b 1 := by
    have hh : B.δ 0 tri.simplex =
        (SSet.Truncated.Edge.id (X := (truncation 2).obj B) b).edge := tri.d₀
    exact hh.trans (pinchedConstant_one b).symm
  have hs₀ : B.δ 1 (kanCosliceFiberEdge a b s).edge = SSet.yonedaEquiv a :=
    (kanCosliceFiberEdge a b s).src_eq
  let G := (joinStdSimplexIso 0 1).hom ≫ SSet.yonedaEquiv.symm tri.simplex
  have hleft : joinInl (Δ[0] : SSet.{u}) Δ[1] ≫ (joinStdSimplexIso 0 1).hom =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  have hfixed : joinInl (Δ[0] : SSet.{u}) Δ[1] ≫ G = a := by
    dsimp only [G]
    rw [← Category.assoc, hleft, Category.assoc,
      stdSimplex.δ_comp_yonedaEquiv_symm]
    change stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm (B.δ 2 tri.simplex) = a
    rw [hd₂, stdSimplex.δ_comp_yonedaEquiv_symm]
    rw [hs₀, Equiv.symm_apply_apply]
  let g := sliceUnderCurry G hfixed
  have hg : g ≫ sliceUnderProjection a = SSet.const b := by
    rw [sliceUnderCurry_projection]
    dsimp only [G]
    rw [← Category.assoc, joinStdSimplexIso_one_inr, stdSimplex.δ_comp_yonedaEquiv_symm]
    change SSet.yonedaEquiv.symm (B.δ 0 tri.simplex) = SSet.const b
    rw [hd₀]
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    rfl
  let f := vertexFiberLift (sliceUnderProjection a) b g hg
  have hf₀ : stdSimplex.δ (1 : Fin 2) ≫ f = SSet.yonedaEquiv.symm s := by
    apply vertexFiber_hom_ext (sliceUnderProjection a) b
    rw [Category.assoc, vertexFiberLift_ι, SSet.yonedaEquiv_symm_comp]
    apply sliceUnderUncurry_injective a
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry, sliceUnderUncurry_yoneda]
    dsimp only [G]
    rw [← Category.assoc, joinStdSimplexIso_vertex_one, Category.assoc,
      stdSimplex.δ_comp_yonedaEquiv_symm]
    change (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (B.δ 2 tri.simplex) = s.val.val
    rw [hd₂]
    change (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm
      (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ s.val.val)) = s.val.val
    rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  have hf₁ : stdSimplex.δ (0 : Fin 2) ≫ f = SSet.yonedaEquiv.symm t := by
    apply vertexFiber_hom_ext (sliceUnderProjection a) b
    rw [Category.assoc, vertexFiberLift_ι, SSet.yonedaEquiv_symm_comp]
    apply sliceUnderUncurry_injective a
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry, sliceUnderUncurry_yoneda]
    dsimp only [G]
    rw [← Category.assoc, joinStdSimplexIso_vertex_one, Category.assoc,
      stdSimplex.δ_comp_yonedaEquiv_symm]
    change (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (B.δ 1 tri.simplex) = t.val.val
    rw [hd₁]
    change (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm
      (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ t.val.val)) = t.val.val
    rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  refine ⟨{ edge := SSet.yonedaEquiv f, src_eq := ?_, tgt_eq := ?_ }⟩
  · change (vertexFiber (sliceUnderProjection a) b).δ 1 (SSet.yonedaEquiv f) = s
    rw [← stdSimplex.yonedaEquiv_δ_comp, hf₀, Equiv.apply_symm_apply]
  · change (vertexFiber (sliceUnderProjection a) b).δ 0 (SSet.yonedaEquiv f) = t
    rw [← stdSimplex.yonedaEquiv_δ_comp, hf₁, Equiv.apply_symm_apply]

/-- 概要：同じホモトピー類の基底の辺は固定終点の coslice fiber 内で同型。
方針：hB の等式を二切断の辺の左ホモトピーへ戻し、fiber の辺と Kan 性を使う。
規約：B は quasicategory。比較するのは同じ始点と終点を持つ辺。
使われ方：指定自然変換の h での等式から輸送の比較への入力。 -/
lemma kanCosliceFiber_nonempty_iso_of_homMk_eq {B : SSet.{u}} [Quasicategory B]
    (a : (Δ[0] : SSet.{u}) ⟶ B) (b : B _⦋0⦌)
    (s t : (vertexFiber (sliceUnderProjection a) b) _⦋0⦌)
    (h : SSet.Truncated.HomotopyCategory.homMk (kanCosliceFiberEdge a b s) =
      SSet.Truncated.HomotopyCategory.homMk (kanCosliceFiberEdge a b t)) :
    Nonempty (VertexIso s t) := by
  have h₂ : SSet.Truncated.HomotopyCategory₂.homMk (kanCosliceFiberEdge a b s) =
      SSet.Truncated.HomotopyCategory₂.homMk (kanCosliceFiberEdge a b t) := by
    have hh := congrArg (fun m ↦ (pathToEdgeHomotopyCategory ((truncation 2).obj B)).map m) h
    simpa only [pathToEdgeHomotopyCategory,
      SSet.Truncated.HomotopyCategory.lift_map_homMk] using hh
  have hh : SSet.Truncated.HomotopicL (kanCosliceFiberEdge a b s)
      (kanCosliceFiberEdge a b t) := Quotient.exact h₂
  obtain ⟨e⟩ := kanCosliceFiber_nonempty_edge_of_homotopicL a b s t hh
  have := cofinalVertexFiber_kanComplex_of_leftFibration (sliceUnderProjection a) b
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk e) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj (vertexFiber (sliceUnderProjection a) b)) _
  exact ⟨asIso (SSet.Truncated.HomotopyCategory.homMk e)⟩

/-- 概要：基底の辺の h での等式から、輸送先の厳密な fiber 内の同型を得る。
方針：基底の coslice fiber の同型を得て、trivial Kan fibration に沿って持ち上げる。
規約：基底 B は quasicategory、p は cocartesian fibration。
使われ方：右比較錐の指定自然変換のホモトピー不変性の一般部分。 -/
lemma kanTransportBaseFiberTarget_nonempty_iso_of_homMk_eq
    {E B : SSet.{u}} [Quasicategory B]
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [CocartesianHornFibration p]
    (b : B _⦋0⦌) (t v : (kanTransportBaseFiber a p b) _⦋0⦌)
    (h : SSet.Truncated.HomotopyCategory.homMk
        (kanCosliceFiberEdge (a ≫ p) b ((kanTransportBaseFiberMap a p b).app _ t)) =
      SSet.Truncated.HomotopyCategory.homMk
        (kanCosliceFiberEdge (a ≫ p) b ((kanTransportBaseFiberMap a p b).app _ v))) :
    Nonempty (VertexIso ((kanTransportBaseFiberTarget a p b).app _ t)
      ((kanTransportBaseFiberTarget a p b).app _ v)) := by
  obtain ⟨e⟩ := kanCosliceFiber_nonempty_iso_of_homMk_eq (a ≫ p) b _ _ h
  exact ⟨kanTransportBaseFiberTargetIso a p b t v e⟩

end SerrePositivity.InfinityCategories
