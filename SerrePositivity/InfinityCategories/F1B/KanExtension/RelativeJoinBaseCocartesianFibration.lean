module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinBaseCocartesianEdges
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinBaseInnerFibration
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinCocartesianFibration

/-!
概要：cocartesian fibration の相対 join の底への射影も cocartesian fibration。
方針：区間成分で頂点を両端に分け、左端は元の輸送、右端は底の辺で持ち上げる。
規約：底の quasicategory 性は不要。
使われ方：余錐の関手の族の全空間を cartesian fibration として扱う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：相対 join の時刻一の頂点は右因子の頂点から来る。
方針：一 fiber の同型で頂点を右因子へ戻す。
規約：二つの構造射は任意。
使われ方：右端を始点とする底の辺の持ち上げ。 -/
lemma kanRelativeJoin_vertex_inr_of_projection_one {X Y S : SSet.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (x : (relativeJoin f g) _⦋0⦌)
    (hx : (relativeJoinProjection f g).app (Opposite.op ⦋0⦌) x =
      stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :
    ∃ y : Y _⦋0⦌, (relativeJoinInr f g).app (Opposite.op ⦋0⦌) y = x := by
  let z : (vertexFiber (relativeJoinProjection f g)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) _⦋0⦌ :=
    ⟨x, by simpa only [PinchedHom.constant_zero] using hx⟩
  let y := (relativeJoinOneFiberIso f g).inv.app (Opposite.op ⦋0⦌) z
  have hi := ConcreteCategory.congr_hom
    (NatTrans.congr_app (relativeJoinOneFiberIso f g).inv_hom_id (Opposite.op ⦋0⦌)) z
  change (relativeJoinOneFiberIso f g).hom.app (Opposite.op ⦋0⦌) y = z at hi
  have he := congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) y)
    (relativeJoinOneFiberIso_hom_ι f g)
  refine ⟨y, he.symm.trans ?_⟩
  exact congrArg (fun v ↦ (vertexFiberι (relativeJoinProjection f g)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌) v) hi

/-- 概要：cocartesian fibration の相対 join の底への射影は cocartesian fibration。
方針：頂点を時刻零と一に分け、両端の cocartesian 辺を使う。
規約：区間への射影ではなく共通の底 C への射影についての主張。
使われ方：相対 join 上の図式の相対指数の cartesian fibration 性。 -/
instance kanRelativeJoinBaseProjection_cocartesianFibration {K C : SSet.{u}}
    (p : K ⟶ C) [CocartesianFibration p] :
    CocartesianFibration (relativeJoinBaseProjection p (𝟙 C)) where
  mem := by
    refine ⟨InnerFibration.mem, ?_⟩
    intro x b hb
    have ht : (relativeJoinProjection p (𝟙 C)).app (Opposite.op ⦋0⦌) x =
        stdSimplex.obj₀Equiv.symm (0 : Fin 2) ∨
        (relativeJoinProjection p (𝟙 C)).app (Opposite.op ⦋0⦌) x =
          stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
      let t := stdSimplex.obj₀Equiv ((relativeJoinProjection p (𝟙 C)).app (Opposite.op ⦋0⦌) x)
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
    · obtain ⟨y, hy⟩ := SerrePositivity.InfinityCategories.relativeJoin_vertex_inl_of_projection_zero p (𝟙 C) x ht
      have hv : (relativeJoinBaseProjection p (𝟙 C)).app (Opposite.op ⦋0⦌) x =
          p.app (Opposite.op ⦋0⦌) y := by
        rw [← hy]
        exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) y)
          (kanRelativeJoinInl_baseProjection p (𝟙 C))
      obtain ⟨l, hl, hlp, hlc⟩ := CocartesianFibration.mem (p := p) |>.2 y b (by
        rw [hb, hv])
      refine ⟨l ≫ relativeJoinInl p (𝟙 C), ?_, ?_, ?_⟩
      · rw [← Category.assoc, hl, SSet.yonedaEquiv_symm_comp, hy]
      · rw [Category.assoc, kanRelativeJoinInl_baseProjection, hlp]
      · rw [SSet.yonedaEquiv_comp]
        exact kanRelativeJoinInl_base_isCocartesianEdge p _ hlc
    · obtain ⟨y, hy⟩ := kanRelativeJoin_vertex_inr_of_projection_one p (𝟙 C) x ht
      have hv : (relativeJoinBaseProjection p (𝟙 C)).app (Opposite.op ⦋0⦌) x = y := by
        rw [← hy]
        exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) y)
          (relativeJoinInr_baseProjection p (𝟙 C))
      refine ⟨b ≫ relativeJoinInr p (𝟙 C), ?_, ?_, ?_⟩
      · rw [← Category.assoc, hb, hv, SSet.yonedaEquiv_symm_comp, hy]
      · rw [Category.assoc, relativeJoinInr_baseProjection, Category.comp_id]
      · rw [SSet.yonedaEquiv_comp]
        exact kanRelativeJoinInr_base_isCocartesianEdge p _

end SerrePositivity.InfinityCategories.F1B
