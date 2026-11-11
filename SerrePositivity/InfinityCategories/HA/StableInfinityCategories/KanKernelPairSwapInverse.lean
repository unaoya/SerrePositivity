module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairSwapPath

/-! # 自己引き戻しの成分交換とループの逆射

概要：可縮な全空間の自己引き戻しの成分交換は、ループ比較で逆射に対応する。
方針：固定 fiber で代表し、交換を戻す辺の二成分の底への像の一致を用いる。
規約：逆射は底のホモトピー圏の逆射。使われ方：懸垂の二枝交換の負号の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：同じ一次単体を持つ辺の類は両端の等号輸送と可換。
方針：両端の等号を消して辺の外延性を使う。
規約：値域の quasicategory 性は不要。使われ方：底で一致する持ち上げ辺の射の比較。 -/
lemma stableHomMk_eqToHom_naturality_of_edge_eq {X : SSet.{u}}
    {x y x' y' : X _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (b : SSet.Truncated.Edge (X := (truncation 2).obj X) x' y')
    (hx : x = x') (hy : y = y') (h : a.edge = b.edge) :
    eqToHom (congrArg (fun v => (SSet.HomotopyCategory.mk v : hoFunctor.obj X)) hx) ≫
      SSet.Truncated.HomotopyCategory.homMk b =
    SSet.Truncated.HomotopyCategory.homMk a ≫
      eqToHom (congrArg (fun v => (SSet.HomotopyCategory.mk v : hoFunctor.obj X)) hy) := by
  subst x'
  subst y'
  have hab : a = b := SSet.Truncated.Edge.ext h
  subst b
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：交換を戻す二辺の底への像が一致すれば、二つの固定 fiber のループの合成は恒等。
方針：始対象からの射の一意性と辺の両端輸送を使って合成を計算する。
規約：この計算自体は両空間の quasicategory 性だけを使う。使われ方：交換の逆射公式。 -/
lemma leftFibrationInitialVertexHom_comp_eq_id_of_edge_pair
    {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (r : E ⟶ B) (e : E _⦋0⦌) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex e)
    (s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r (r.app (Opposite.op ⦋0⦌) e)) _⦋0⦌)
    (a : SSet.Truncated.Edge (X := (truncation 2).obj E) e t.val)
    (b : SSet.Truncated.Edge (X := (truncation 2).obj E) s.val e)
    (hab : r.app (Opposite.op ⦋1⦌) a.edge = r.app (Opposite.op ⦋1⦌) b.edge) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialVertexHom r e he (r.app (Opposite.op ⦋0⦌) e) s ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialVertexHom r e he (r.app (Opposite.op ⦋0⦌) e) t =
    𝟙 (SSet.HomotopyCategory.mk (r.app (Opposite.op ⦋0⦌) e) : hoFunctor.obj B) := by
  have hs := s.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero (r.app (Opposite.op ⦋0⦌) e))
  have ht := t.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero (r.app (Opposite.op ⦋0⦌) e))
  have h := stableHomMk_eqToHom_naturality_of_edge_eq
    (b.map ((truncation 2).map r)) (a.map ((truncation 2).map r)) hs ht.symm hab.symm
  have ha : he.isInitialHo.to (SSet.HomotopyCategory.mk t.val) =
      SSet.Truncated.HomotopyCategory.homMk a := he.isInitialHo.hom_ext _ _
  have hb : he.isInitialHo.to (SSet.HomotopyCategory.mk s.val) ≫
      SSet.Truncated.HomotopyCategory.homMk b =
      𝟙 (SSet.HomotopyCategory.mk e : hoFunctor.obj E) := he.isInitialHo.hom_ext _ _
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialVertexHom]
  rw [ha]
  change ((hoFunctor.map r).toFunctor.map (he.isInitialHo.to (SSet.HomotopyCategory.mk s.val)) ≫
    eqToHom (congrArg (fun v => (SSet.HomotopyCategory.mk v : hoFunctor.obj B)) hs)) ≫
      (SSet.Truncated.HomotopyCategory.homMk (a.map ((truncation 2).map r)) ≫
        eqToHom (congrArg (fun v => (SSet.HomotopyCategory.mk v : hoFunctor.obj B)) ht)) = _
  rw [Category.assoc, ← Category.assoc (eqToHom _) _ _, h, Category.assoc,
    eqToHom_trans]
  simp only [eqToHom_refl, Category.comp_id]
  change (hoFunctor.map r).toFunctor.map (he.isInitialHo.to (SSet.HomotopyCategory.mk s.val)) ≫
    (hoFunctor.map r).toFunctor.map (SSet.Truncated.HomotopyCategory.homMk b) = _
  rw [← Functor.map_comp, hb]
  exact CategoryTheory.Functor.map_id _ _

/-- 概要：自己引き戻しの成分と交換された成分のループの積は恒等射。
方針：全単射である固定 fiber 包含で代表し、辺の持ち上げと合成公式を適用する。
規約：r は Kan fibration、E と B は Kan、E は可縮。使われ方：逆射としての交換の同定。 -/
lemma kanKernelPairPiZeroLoopEquiv_comp_swap {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (r : E ⟶ B) [Fibration r] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌)
    (c : SSet.π₀ (pullback r r)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv r hE e c ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv r hE e (SSet.mapπ₀ (pullbackSymmetry r r).hom c) = 𝟙 _ := by
  obtain ⟨c, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairFiberInclusion_piZero_bijective r hE e).surjective c
  obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective c
  obtain ⟨t, a, b, hab, hswap⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_kanKernelPairSwap_fiber_path r hE e s
  rw [hswap, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_fiber_mk, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_fiber_mk]
  exact leftFibrationInitialVertexHom_comp_eq_id_of_edge_pair r e (hE.isInitialVertex e) s t a b hab

/-- 概要：ループ比較の値は底のホモトピー圏で可逆。
方針：Kan 複体のホモトピー圏の全ての射が可逆であることを使う。
規約：比較の仮定をそのまま保つ。使われ方：交換公式の逆射を型付けする。 -/
instance kanKernelPairPiZeroLoopEquiv_isIso {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (r : E ⟶ B) [Fibration r] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌)
    (c : SSet.π₀ (pullback r r)) : IsIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv r hE e c) :=
  IsGroupoid.all_isIso (C := hoFunctor.obj B) _

/-- 概要：自己引き戻しの二成分交換はループ比較により基点の自己射の逆射となる。
方針：交換との積の恒等式を底のホモトピー圏の亜群で解く。
規約：可縮な全空間と基点の選択を固定する。使われ方：懸垂交換の符号の同定。 -/
lemma kanKernelPairPiZeroLoopEquiv_swap {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (r : E ⟶ B) [Fibration r] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌)
    (c : SSet.π₀ (pullback r r)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv r hE e (SSet.mapπ₀ (pullbackSymmetry r r).hom c) =
      inv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv r hE e c) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv r hE e c)).1
  rw [kanKernelPairPiZeroLoopEquiv_comp_swap, IsIso.hom_inv_id]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
