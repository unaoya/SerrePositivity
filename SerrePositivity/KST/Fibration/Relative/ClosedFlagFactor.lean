module
public import SerrePositivity.KST.Fibration.Relative.ClosedFlagConstants
public import SerrePositivity.KST.Fibration.StandardTailAttachment

/-!
概要：相対旗の全体持ち上げ条件を貼り合わせで扱う狭い界面。
方針：元の wide 包含の inner fibration 性と標準単体の部分複体を使う。
規約：商への因子分解を使用しない。使われ方：有限旗の相対加法性の帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：全可逆辺は元の W に属する。方針：同じ安定閉包の既存定理。
規約：P 自身への所属。使われ方：退化辺の処理。 -/
lemma closedStableEdges_of_invertible {B : StableModel.{u}} (P : ClosedStablePredicate B)
    {a : B.carrier _⦋1⦌} (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a)) : a ∈ closedStableEdges P := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_of_isInvertible {x | P.predicate x} ha
  simpa only [closedStableEdges,
    show {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure {x | P.predicate x} x} = {x | P.predicate x} from
    Set.ext (closedStableClosure_iff P)] using h

/-- 概要：一単体での wide 条件は元の W 辺条件と等しい。
方針：恒等制限と退化制限を分ける。規約：全退化を含む。
使われ方：最後の一辺の全体持ち上げ条件。 -/
lemma closedStableWide_edge_iff {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (a : B.carrier _⦋1⦌) :
    a ∈ (closedStableWide P).obj (Opposite.op ⦋1⦌) ↔ a ∈ closedStableEdges P := by
  constructor
  · intro h
    simpa only [op_id, CategoryTheory.Functor.map_id_apply] using h (𝟙 ⦋1⦌)
  · intro h θ
    rcases SimplexCategory.eq_of_one_to_one θ with ⟨j, rfl⟩ | rfl
    · let v := B.carrier.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ j).op a
      have he : B.carrier.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ j).op a =
          B.carrier.σ 0 v := by
        change _ = B.carrier.map (SimplexCategory.σ (0 : Fin 1)).op
          (B.carrier.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ j).op a)
        have hc : SimplexCategory.const ⦋1⦌ ⦋1⦌ j =
            SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.const ⦋0⦌ ⦋1⦌ j := rfl
        rw [hc, op_comp, CategoryTheory.Functor.map_comp]
        rfl
      rw [he]
      exact closedStableEdges_of_invertible P (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_degenerate v)
    · simpa only [op_id, CategoryTheory.Functor.map_id_apply] using h

/-- 概要：標準単体の条件と同じ実図式の wide への因子分解。
方針：標準単体の像部分複体と lift の公開 API。
規約：元の関手を厳密に回収。使われ方：全旗を貼り合わせる。 -/
lemma closedFlag_factor_iff {B : StableModel.{u}} (P : ClosedStablePredicate B) (n : ℕ)
    (f : (Δ[n] : SSet.{u}) ⟶ B.carrier) :
    closedFlagPredicate P ⦋n⦌ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) ↔
      ∃ g : (Δ[n] : SSet.{u}) ⟶ (closedStableWide P : SSet.{u}),
        g ≫ (closedStableWide P).ι = f := by
  change SSet.yonedaEquiv f ∈ (closedStableWide P).obj _ ↔ _
  constructor
  · intro h
    have hr : Subcomplex.range f ≤ closedStableWide P := by
      rw [Subcomplex.range_eq_ofSimplex]
      exact (Subcomplex.ofSimplex_le_iff _ _).2 h
    exact ⟨(closedStableWide P).lift f hr, Subcomplex.lift_ι _ _⟩
  · rintro ⟨g, rfl⟩
    exact (SSet.yonedaEquiv g).property

/-- 概要：内 anodyne 制限後の W 持ち上げは元の全図式を保って延長できる。
方針：同じ wide 包含の持ち上げ性。規約：商なし。
使われ方：最後の辺を貼った旗の全 W 条件の反映。 -/
lemma closedWideFactor_of_innerAnodyne {B : StableModel.{u}} (P : ClosedStablePredicate B)
    {K L : SSet.{u}} (i : K ⟶ L) (hi : innerAnodyneExtensions i) (f : L ⟶ B.carrier)
    (g : K ⟶ (closedStableWide P : SSet.{u})) (hg : g ≫ (closedStableWide P).ι = i ≫ f) :
    ∃ G : L ⟶ (closedStableWide P : SSet.{u}), G ≫ (closedStableWide P).ι = f := by
  have := hi (closedStableWide P).ι (InnerFibration.mem (q := (closedStableWide P).ι))
  let sq : CommSq g i (closedStableWide P).ι f := ⟨hg⟩
  exact ⟨sq.lift, sq.fac_right⟩

end SerrePositivity.KST.Fibration.Relative
