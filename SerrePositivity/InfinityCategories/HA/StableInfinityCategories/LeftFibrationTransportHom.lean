module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransportLift
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairSwapInverse

/-! # Fiber 輸送の Hom 表示と後合成

概要：始対象を持つ left fibration の fiber の輸送は、Hom 表示で底の辺との後合成になる。
方針：輸送の各頂点の辺を底へ送り、始対象からの射の一意性と端点の輸送を使う。
規約：選んだ輸送の区間族をそのまま使う。使われ方：余錐空間の輸送と Hom の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：fiber 輸送の区間族を包含の間の単体的ホモトピーとして読む。
方針：保持している両端の等号をホモトピーのデータに入れる。
規約：相対部分は空。使われ方：各頂点における輸送辺の構成。 -/
def LeftFibrationFiberTransport.homotopy {E B : SSet.{u}} {p : E ⟶ B}
    {x y : B _⦋0⦌} {a : SSet.Truncated.Edge (X := (truncation 2).obj B) x y}
    (T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport p a) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x) (T.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p y) where
  h := T.h
  h₀ := T.h₀
  h₁ := T.h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 概要：fiber 輸送は各頂点から輸送された頂点への辺を与える。
方針：包含の間のホモトピーの頂点上の辺を取る。
規約：辺は元の全空間にある。使われ方：始対象からの射の合成の計算。 -/
def LeftFibrationFiberTransport.vertexEdge {E B : SSet.{u}} {p : E ⟶ B}
    {x y : B _⦋0⦌} {a : SSet.Truncated.Edge (X := (truncation 2).obj B) x y}
    (T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport p a) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) _⦋0⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj E) s.val
      ((T.map.app (Opposite.op ⦋0⦌) s).val) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge T.homotopy s).toTruncated

/-- 概要：輸送の頂点の辺は底に送ると指定した底の辺そのものになる。
方針：区間族の底への等式を頂点の恒等辺と標準区間の辺で評価する。
規約：ホモトピー類だけでなく一次単体の等号。使われ方：Hom 表示の後合成の式。 -/
lemma LeftFibrationFiberTransport.vertexEdge_over {E B : SSet.{u}} {p : E ⟶ B}
    {x y : B _⦋0⦌} {a : SSet.Truncated.Edge (X := (truncation 2).obj B) x y}
    (T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport p a) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) _⦋0⦌) :
    p.app (Opposite.op ⦋1⦌) (T.vertexEdge s).edge = a.edge := by
  let w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x ⊗ (Δ[1] : SSet.{u})) _⦋1⦌ :=
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x)) s).edge,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u}.edge)
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app T.over (Opposite.op ⦋1⦌)) w
  change p.app (Opposite.op ⦋1⦌) (T.h.app (Opposite.op ⦋1⦌) w) =
    (SSet.yonedaEquiv.symm a.edge).app (Opposite.op ⦋1⦌) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge at h
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u}.edge = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  have hz : (SSet.yonedaEquiv.symm a.edge).app (Opposite.op ⦋1⦌)
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge = a.edge := by
    calc
      _ = (SSet.yonedaEquiv.symm a.edge).app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) :=
        congrArg ((SSet.yonedaEquiv.symm a.edge).app (Opposite.op ⦋1⦌)) hi
      _ = SSet.yonedaEquiv (SSet.yonedaEquiv.symm a.edge) := by
        exact (SSet.yonedaEquiv_comp (𝟙 (Δ[1] : SSet.{u}))
          (SSet.yonedaEquiv.symm a.edge)).symm
      _ = _ := (SSet.yonedaEquiv (X := B) (n := ⦋1⦌)).apply_symm_apply a.edge
  exact h.trans hz

/-- 概要：始対象による fiber の Hom 表示は、輸送を底の辺との後合成へ送る。
方針：各頂点で輸送辺を取り、底の辺との一致と始対象からの一意の射の合成を比較する。
規約：全空間と底は quasicategory、射は left fibration、始点は始対象。
使われ方：余極限余錐の Hom 表示の終点についての自然性。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_transport {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (e : E _⦋0⦌) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex e) {x y : B _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj B) x y)
    (T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport p a) (c : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialFiberPiZeroEquiv p e he y (SSet.mapπ₀ T.map c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialFiberPiZeroEquiv p e he x c ≫
        SSet.Truncated.HomotopyCategory.homMk a := by
  obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective c
  rw [SSet.mapπ₀_mk, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialFiberPiZeroEquiv_mk,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialFiberPiZeroEquiv_mk]
  let t := T.map.app (Opposite.op ⦋0⦌) s
  let v := T.vertexEdge s
  have hs := s.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero x)
  have ht := t.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero y)
  have hv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomMk_eqToHom_naturality_of_edge_eq (v.map ((truncation 2).map p)) a
    hs ht (T.vertexEdge_over s)
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialVertexHom]
  rw [Category.assoc, hv, ← Category.assoc]
  change (hoFunctor.map p).toFunctor.map (he.isInitialHo.to (SSet.HomotopyCategory.mk t.val)) ≫
    eqToHom _ =
    ((hoFunctor.map p).toFunctor.map (he.isInitialHo.to (SSet.HomotopyCategory.mk s.val)) ≫
      (hoFunctor.map p).toFunctor.map (SSet.Truncated.HomotopyCategory.homMk v)) ≫ eqToHom _
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun k : (SSet.HomotopyCategory.mk e : hoFunctor.obj E) ⟶
      SSet.HomotopyCategory.mk t.val => (hoFunctor.map p).toFunctor.map k ≫
    eqToHom (congrArg (fun z => (SSet.HomotopyCategory.mk z : hoFunctor.obj B)) ht))
    (he.isInitialHo.hom_ext _ _)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
