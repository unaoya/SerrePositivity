module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinBaseCocartesianEdges
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinBaseInnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCocartesianFibration

/-!
概要：cocartesian fibration の相対 join の底への射影も cocartesian fibration。
方針：区間成分で頂点を両端に分け、左端は元の輸送、右端は底の辺で持ち上げる。
規約：底の quasicategory 性は不要。
使われ方：余錐の関手の族の全空間を cartesian fibration として扱う。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：相対 join の時刻一の頂点は右因子の頂点から来る。
方針：一 fiber の同型で頂点を右因子へ戻す。
規約：二つの構造射は任意。
使われ方：右端を始点とする底の辺の持ち上げ。 -/
lemma kanRelativeJoin_vertex_inr_of_projection_one {X Y S : SSet.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f g) _⦋0⦌)
    (hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g).app (Opposite.op ⦋0⦌) x =
      stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :
    ∃ y : Y _⦋0⦌, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f g).app (Opposite.op ⦋0⦌) y = x := by
  let z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) _⦋0⦌ :=
    ⟨x, by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero] using hx⟩
  let y := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinOneFiberIso f g).inv.app (Opposite.op ⦋0⦌) z
  have hi := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinOneFiberIso f g).inv_hom_id (Opposite.op ⦋0⦌)) z
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinOneFiberIso f g).hom.app (Opposite.op ⦋0⦌) y = z at hi
  have he := congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinOneFiberIso_hom_ι f g)
  refine ⟨y, he.symm.trans ?_⟩
  exact congrArg (fun v ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌) v) hi

/-- 概要：cocartesian fibration の相対 join の底への射影は cocartesian fibration。
方針：頂点を時刻零と一に分け、両端の cocartesian 辺を使う。
規約：区間への射影ではなく共通の底 C への射影についての主張。
使われ方：相対 join 上の図式の相対指数の cartesian fibration 性。 -/
instance kanRelativeJoinBaseProjection_cocartesianFibration {K C : SSet.{u}}
    (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) where
  mem := by
    refine ⟨InnerFibration.mem, ?_⟩
    intro x b hb
    have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection p (𝟙 C)).app (Opposite.op ⦋0⦌) x =
        stdSimplex.obj₀Equiv.symm (0 : Fin 2) ∨
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection p (𝟙 C)).app (Opposite.op ⦋0⦌) x =
          stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
      let t := stdSimplex.obj₀Equiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection p (𝟙 C)).app (Opposite.op ⦋0⦌) x)
      have h : t = 0 ∨ t = 1 := by
        have ht : t.val < 2 := t.isLt
        by_cases hz : t.val = 0
        · exact Or.inl (Fin.ext hz)
        · have hv : t.val = 1 := by omega
          exact Or.inr (Fin.ext hv)
      rcases h with h | h
      · left
        apply stdSimplex.obj₀Equiv.injective
        simpa only [Equiv.apply_symm_apply] using h
      · right
        apply stdSimplex.obj₀Equiv.injective
        simpa only [Equiv.apply_symm_apply] using h
    rcases ht with ht | ht
    · obtain ⟨y, hy⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_vertex_inl_of_projection_zero p (𝟙 C) x ht
      have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)).app (Opposite.op ⦋0⦌) x =
          p.app (Opposite.op ⦋0⦌) y := by
        rw [← hy]
        exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) y)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInl_baseProjection p (𝟙 C))
      obtain ⟨l, hl, hlp, hlc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration.mem (p := p) |>.2 y b (by
        rw [hb, hv])
      refine ⟨l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C), ?_, ?_, ?_⟩
      · rw [← Category.assoc, hl, SSet.yonedaEquiv_symm_comp, hy]
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInl_baseProjection, hlp]
      · rw [SSet.yonedaEquiv_comp]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInl_base_isCocartesianEdge p _ hlc
    · obtain ⟨y, hy⟩ := kanRelativeJoin_vertex_inr_of_projection_one p (𝟙 C) x ht
      have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)).app (Opposite.op ⦋0⦌) x = y := by
        rw [← hy]
        exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) y)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_baseProjection p (𝟙 C))
      refine ⟨b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 C), ?_, ?_, ?_⟩
      · rw [← Category.assoc, hb, hv, SSet.yonedaEquiv_symm_comp, hy]
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_baseProjection, Category.comp_id]
      · rw [SSet.yonedaEquiv_comp]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInr_base_isCocartesianEdge p _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
