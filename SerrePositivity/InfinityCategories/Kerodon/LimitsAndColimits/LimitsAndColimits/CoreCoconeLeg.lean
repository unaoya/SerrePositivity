module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Coslice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-! # 余錐の脚と余錐間の辺の可換三角形

概要：余錐の各脚を端点つきの辺で表し、余錐間の辺との合成三角形を構成する。
方針：点と辺の join を標準二単体へ移し、coslice の一次単体を制限する。
規約：端点の等号の輸送を構造に含める。使われ方：二項余積の Hom の普遍性。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：余錐の指定した頂点から余錐頂点への脚。
方針：その頂点と余錐頂点の二点の join へ制限する。
規約：始点は指定点の図式での像。使われ方：余錐の脚のホモトピー類。 -/
def JoinCocone.leg {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (i : (Δ[0] : SSet.{u}) ⟶ K) :
    SSet.Truncated.Edge (X := (truncation 2).obj X) (SSet.yonedaEquiv (i ≫ p)) c.vertex where
  edge := SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0]) ≫ c.val)
  src_eq := by
    change X.δ 1 (SSet.yonedaEquiv _) = SSet.yonedaEquiv (i ≫ p)
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl,
      Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap,
      Category.assoc, c.property]
  tgt_eq := by
    change X.δ 0 (SSet.yonedaEquiv _) = c.vertex
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr,
      Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap,
      Category.id_comp]
    rfl

/-- 概要：点と辺の join の逆同型は二つの端点の制限と可換。
方針：既存の順方向の式に二つの逆同型を合成する。
規約：i=1 は最初の辺、i=0 は長辺。使われ方：余錐の辺の二つの端点。 -/
lemma joinStdSimplexIso_vertex_one_inv (i : Fin 2) :
    stdSimplex.δ i.succ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ i) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_vertex_one, Iso.inv_hom_id_assoc]

/-- 概要：余錐間の辺を指定した脚へ制限すると合成を表す二単体が得られる。
方針：coslice の一次単体を uncurry し、指定点と区間の join に制限する。
規約：quasicategory 性は不要。使われ方：h C での余錐射の可換式。 -/
def JoinCocone.legCompStruct {K X : SSet.{u}} {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) c d)
    (i : (Δ[0] : SSet.{u}) ⟶ K) :
    (c.leg i).CompStruct (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p))) (d.leg i) := by
  let a : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p := SSet.yonedaEquiv.symm e.edge
  let U : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[1] : SSet.{u}) ⟶ X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry a
  have ha₀ : stdSimplex.δ (1 : Fin 2) ≫ a = SSet.yonedaEquiv.symm c := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    exact e.src_eq.trans ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (n := ⦋0⦌)).apply_symm_apply c).symm
  have ha₁ : stdSimplex.δ (0 : Fin 2) ≫ a = SSet.yonedaEquiv.symm d := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    exact e.tgt_eq.trans ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (n := ⦋0⦌)).apply_symm_apply d).symm
  let T : (Δ[2] : SSet.{u}) ⟶ X :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[1]) ≫ U
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.δ (1 : Fin 2)) ≫ U = c.val := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, ha₀, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.δ (0 : Fin 2)) ≫ U = d.val := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, ha₁, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
  have hface (j : Fin 2) : stdSimplex.δ j.succ ≫ T =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0]) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.δ j) ≫ U) := by
    change _ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[1]) ≫ U) = _
    rw [← Category.assoc, joinStdSimplexIso_vertex_one_inv]
    have hjoin : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ j) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 (Δ[1] : SSet.{u})) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 (Δ[0] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.δ j) := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
      simp only [Category.id_comp, Category.comp_id]
    rw [Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ j)),
      hjoin, Category.assoc]
  have h₂ : stdSimplex.δ (2 : Fin 3) ≫ T =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0]) ≫ c.val := by
    have h := hface (1 : Fin 2)
    change stdSimplex.δ (2 : Fin 3) ≫ T = _ at h
    rw [h₀] at h
    exact h
  have h₁' : stdSimplex.δ (1 : Fin 3) ≫ T =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0]) ≫ d.val := by
    have h := hface (0 : Fin 2)
    change stdSimplex.δ (1 : Fin 3) ≫ T = _ at h
    rw [h₁] at h
    exact h
  have h₀' : stdSimplex.δ (0 : Fin 3) ≫ T =
      SSet.yonedaEquiv.symm e.edge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p := by
    have hshape : stdSimplex.δ (0 : Fin 3) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[1] := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_inr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change _ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[1]) ≫ U) = _
    rw [← Category.assoc, hshape, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection (SSet.yonedaEquiv.symm e.edge)
  refine { simplex := SSet.yonedaEquiv T, d₂ := ?_, d₀ := ?_, d₁ := ?_ }
  · change X.δ 2 (SSet.yonedaEquiv T) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, h₂]
    rfl
  · change X.δ 0 (SSet.yonedaEquiv T) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, h₀', SSet.yonedaEquiv_comp]
    exact congrArg (fun a => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p).app (Opposite.op ⦋1⦌) a)
      ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (n := ⦋1⦌)).apply_symm_apply e.edge)
  · change X.δ 1 (SSet.yonedaEquiv T) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, h₁']
    rfl

/-- 概要：余錐間の辺の頂点成分は、各脚との合成を可換にする。
方針：指定脚の合成二単体をホモトピー圏で読む。
規約：quasicategory 性は不要。使われ方：二項余積からの射の因子分解。 -/
lemma JoinCocone.leg_comp_projection {K X : SSet.{u}} {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) c d)
    (i : (Δ[0] : SSet.{u}) ⟶ K) :
    SSet.Truncated.HomotopyCategory.homMk (c.leg i) ≫
      SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p))) =
        SSet.Truncated.HomotopyCategory.homMk (d.leg i) :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk (JoinCocone.legCompStruct e i)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
