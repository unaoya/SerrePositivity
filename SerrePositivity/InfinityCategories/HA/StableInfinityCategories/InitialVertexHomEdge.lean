module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairSwapInverse

/-! # 始対象による Hom 表示と fiber 頂点間の辺

概要：底の辺を表す全空間の辺で二つの fiber 頂点が結ばれれば、Hom 表示はその底の辺との後合成で変わる。
方針：始対象からの射の一意性と辺の両端の等号輸送を使う。
規約：全体の区間族の選択は不要。使われ方：基点を変えた自己引き戻しのループ表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：底の辺を表す二つの fiber 頂点間の辺は、始対象による Hom 表示を後合成で変える。
方針：底へ送った辺の端点を揃え、始対象からの射の一意性を使う。
規約：全空間は quasicategory、射の充填性は不要。使われ方：fiber 輸送の頂点ごとの計算。 -/
lemma leftFibrationInitialVertexHom_edge {E B : SSet.{u}} [Quasicategory E]
    (p : E ⟶ B) (e : E _⦋0⦌) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex e) {x y : B _⦋0⦌}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) _⦋0⦌) (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p y) _⦋0⦌)
    (v : SSet.Truncated.Edge (X := (truncation 2).obj E) s.val t.val)
    (a : SSet.Truncated.Edge (X := (truncation 2).obj B) x y)
    (hv : p.app (Opposite.op ⦋1⦌) v.edge = a.edge) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialVertexHom p e he y t =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialVertexHom p e he x s ≫ SSet.Truncated.HomotopyCategory.homMk a := by
  have hs := s.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero x)
  have ht := t.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero y)
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomMk_eqToHom_naturality_of_edge_eq (v.map ((truncation 2).map p)) a hs ht hv
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialVertexHom]
  rw [Category.assoc, h, ← Category.assoc]
  change (hoFunctor.map p).toFunctor.map (he.isInitialHo.to (SSet.HomotopyCategory.mk t.val)) ≫
    eqToHom _ =
    ((hoFunctor.map p).toFunctor.map (he.isInitialHo.to (SSet.HomotopyCategory.mk s.val)) ≫
      (hoFunctor.map p).toFunctor.map (SSet.Truncated.HomotopyCategory.homMk v)) ≫ eqToHom _
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun k : (SSet.HomotopyCategory.mk e : hoFunctor.obj E) ⟶
      SSet.HomotopyCategory.mk t.val => (hoFunctor.map p).toFunctor.map k ≫
        eqToHom (congrArg (fun z => (SSet.HomotopyCategory.mk z : hoFunctor.obj B)) ht))
    (he.isInitialHo.hom_ext _ _)

/-- 概要：二つの fiber 頂点を結ぶ辺の底への像は、fiber の π₀ の Hom 表示で後合成として作用する。
方針：連結成分の代表元の公式を頂点の計算に適用する。
規約：底も quasicategory、射は left fibration。使われ方：自己引き戻しの射影後の輸送の公式。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_edge {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (e : E _⦋0⦌) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex e) {x y : B _⦋0⦌}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) _⦋0⦌) (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p y) _⦋0⦌)
    (v : SSet.Truncated.Edge (X := (truncation 2).obj E) s.val t.val)
    (a : SSet.Truncated.Edge (X := (truncation 2).obj B) x y)
    (hv : p.app (Opposite.op ⦋1⦌) v.edge = a.edge) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialFiberPiZeroEquiv p e he y (SSet.π₀.mk t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialFiberPiZeroEquiv p e he x (SSet.π₀.mk s) ≫
        SSet.Truncated.HomotopyCategory.homMk a := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialFiberPiZeroEquiv_mk, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialFiberPiZeroEquiv_mk]
  exact leftFibrationInitialVertexHom_edge p e he s t v a hv

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
