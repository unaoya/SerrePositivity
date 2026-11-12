module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairMap
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairSwapInverse

/-! # 底を変える可換正方形に対するループ比較の自然性

概要：可縮な Kan 全空間の自己引き戻しのループ表示は可換正方形に自然。
方針：固定 fiber の頂点で始対象からの辺を底に送る公式を比較する。
規約：底の基点の等号はホモトピー圏の等号輸送で明示する。使われ方：ループ表示と加法の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：始対象による頂点の Hom 表示は、始対象から選んだ任意の辺の像で計算できる。
方針：始対象からの射の一意性を定義に代入する。
規約：辺の終点は指定 fiber の元そのもの。使われ方：底を変える正方形の代表元の計算。 -/
lemma leftFibrationInitialVertexHom_eq_edge {E B : SSet.{u}} [Quasicategory E]
    (p : E ⟶ B) (e : E _⦋0⦌) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex e) (y : B _⦋0⦌)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p y) _⦋0⦌)
    (a : SSet.Truncated.Edge (X := (truncation 2).obj E) e s.val) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialVertexHom p e he y s =
      SSet.Truncated.HomotopyCategory.homMk (a.map ((truncation 2).map p)) ≫
        eqToHom (congrArg (fun v => (SSet.HomotopyCategory.mk v : hoFunctor.obj B))
          (s.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero y))) := by
  have ha : he.isInitialHo.to (SSet.HomotopyCategory.mk s.val) =
      SSet.Truncated.HomotopyCategory.homMk a := he.isInitialHo.hom_ext _ _
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialVertexHom]
  rw [ha]
  rfl

/-- 概要：固定 fiber の頂点による Hom 表示は底を変える可換正方形に自然。
方針：始対象からの辺を選び、二通りに底へ送った辺の厳密な一致と両端輸送を使う。
規約：始点とその像は始対象、四空間は quasicategory。使われ方：ループ比較の自然性。 -/
lemma leftFibrationInitialVertexHom_square
    {E B E' B' : SSet.{u}} [Quasicategory E] [Quasicategory B]
    [Quasicategory E'] [Quasicategory B']
    (p : E ⟶ B) (q : E' ⟶ B') (f : E ⟶ E') (g : B ⟶ B')
    (h : f ≫ q = p ≫ g) (e : E _⦋0⦌) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex e)
    (he' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (f.app (Opposite.op ⦋0⦌) e))
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (p.app (Opposite.op ⦋0⦌) e)) _⦋0⦌) :
    eqToHom (congrArg (fun v => (SSet.HomotopyCategory.mk v : hoFunctor.obj B'))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairMap_basepoint p q f g h e)) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialVertexHom q (f.app (Opposite.op ⦋0⦌) e) he'
        (q.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) e))
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberMap p q f g h e).app (Opposite.op ⦋0⦌) s) =
    (hoFunctor.map g).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialVertexHom p e he (p.app (Opposite.op ⦋0⦌) e) s) ≫
      eqToHom (congrArg (fun v => (SSet.HomotopyCategory.mk v : hoFunctor.obj B'))
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairMap_basepoint p q f g h e)) := by
  obtain ⟨a⟩ := he.nonempty_edge s.val
  let t := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberMap p q f g h e).app (Opposite.op ⦋0⦌) s
  have htval : t.val = f.app (Opposite.op ⦋0⦌) s.val := rfl
  let a' : SSet.Truncated.Edge (X := (truncation 2).obj E')
      (f.app (Opposite.op ⦋0⦌) e) t.val :=
    { edge := f.app (Opposite.op ⦋1⦌) a.edge
      src_eq := (a.map ((truncation 2).map f)).src_eq
      tgt_eq := (a.map ((truncation 2).map f)).tgt_eq.trans htval.symm }
  have hedges : ((a.map ((truncation 2).map p)).map ((truncation 2).map g)).edge =
      (a'.map ((truncation 2).map q)).edge := by
    change g.app (Opposite.op ⦋1⦌) (p.app (Opposite.op ⦋1⦌) a.edge) =
      q.app (Opposite.op ⦋1⦌) (f.app (Opposite.op ⦋1⦌) a.edge)
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋1⦌)) a.edge).symm
  have hnat := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomMk_eqToHom_naturality_of_edge_eq
    ((a.map ((truncation 2).map p)).map ((truncation 2).map g))
    (a'.map ((truncation 2).map q)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairMap_basepoint p q f g h e)
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairMap_basepoint p q f g h s.val).trans
      (congrArg (q.app (Opposite.op ⦋0⦌)) htval.symm)) hedges
  rw [leftFibrationInitialVertexHom_eq_edge p e he _ s a,
    leftFibrationInitialVertexHom_eq_edge q _ he' _ t a']
  rw [CategoryTheory.Functor.map_comp, eqToHom_map]
  change eqToHom _ ≫ (SSet.Truncated.HomotopyCategory.homMk (a'.map ((truncation 2).map q)) ≫
    eqToHom _) =
    (SSet.Truncated.HomotopyCategory.homMk
      ((a.map ((truncation 2).map p)).map ((truncation 2).map g)) ≫ eqToHom _) ≫ eqToHom _
  rw [← Category.assoc, hnat, Category.assoc, eqToHom_trans, Category.assoc, eqToHom_trans]

/-- 概要：自己引き戻しのループ同値は、底を変える可換正方形に自然。
方針：固定 fiber の包含の π₀ 全射性で代表し、包含の可換性と頂点の自然性を使う。
規約：両全空間は可縮な Kan 複体、両射は Kan fibration、両底も Kan。
使われ方：余錐空間に誘導される写像とループ群演算との比較。 -/
lemma kanKernelPairPiZeroLoopEquiv_naturality
    {E B E' B' : SSet.{u}} [KanComplex E] [KanComplex B]
    [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) [Fibration p] (q : E' ⟶ B') [Fibration q]
    (f : E ⟶ E') (g : B ⟶ B') (h : f ≫ q = p ≫ g)
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (hE' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E')
    (e : E _⦋0⦌) (c : SSet.π₀ (pullback p p)) :
    eqToHom (congrArg (fun v => (SSet.HomotopyCategory.mk v : hoFunctor.obj B'))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairMap_basepoint p q f g h e)) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv q hE' (f.app (Opposite.op ⦋0⦌) e)
        (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairMap p q f g h) c) =
    (hoFunctor.map g).toFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv p hE e c) ≫
      eqToHom (congrArg (fun v => (SSet.HomotopyCategory.mk v : hoFunctor.obj B'))
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairMap_basepoint p q f g h e)) := by
  obtain ⟨c, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion_piZero_bijective p hE e).surjective c
  obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective c
  rw [← SSet.mapπ₀_comp_apply, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberMap_inclusion, SSet.mapπ₀_comp_apply,
    SSet.mapπ₀_mk, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_fiber_mk,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_fiber_mk]
  exact leftFibrationInitialVertexHom_square p q f g h e (hE.isInitialVertex e)
    (hE'.isInitialVertex _) s

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
