module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IntervalCocartesianCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCrossingCocartesian
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinEndpointFibers
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinQuasicategory

/-!
概要：関手の相対 join の区間への射影は cocartesian fibration。
方針：零 fiber を左因子で表示し、標準 prism の垂直辺で区間の標準辺を持ち上げる。
規約：両因子は quasicategory、右因子の構造射は恒等射。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、Theorem 5.2.4.1（Tag 024N） の比較の始域。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：相対 join の時刻零の頂点は左因子の頂点から来る。
方針：頂点を零 fiber に持ち上げ、左因子との標準同型の逆で戻す。
規約：二つの構造射は任意。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、標準 prism の始点の指定。 -/
lemma relativeJoin_vertex_inl_of_projection_zero {X Y S : SSet.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f g) _⦋0⦌)
    (hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g).app (Opposite.op ⦋0⦌) x =
      stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
    ∃ y : X _⦋0⦌, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl f g).app (Opposite.op ⦋0⦌) y = x := by
  let z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) _⦋0⦌ :=
    ⟨x, by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero] using hx⟩
  let y := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinZeroFiberIso f g).inv.app (Opposite.op ⦋0⦌) z
  have hi := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinZeroFiberIso f g).inv_hom_id (Opposite.op ⦋0⦌)) z
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinZeroFiberIso f g).hom.app (Opposite.op ⦋0⦌) y = z at hi
  have he := congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinZeroFiberIso_hom_ι f g)
  refine ⟨y, he.symm.trans ?_⟩
  exact congrArg (fun v ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) v) hi

/-- 概要：二つの quasicategory の間の関手の相対 join は区間上の cocartesian fibration。
方針：零 fiber の各頂点を標準 prism の垂直辺で持ち上げ、区間の判定補題を適用する。
規約：係数の極限・余極限や分類定理は使わない。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、Theorem 5.2.4.1（Tag 024N） の写像円柱比較。 -/
instance relativeJoinProjection_cocartesianFibration {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianFibration_interval_of_lift
  intro x hx
  obtain ⟨y, hy⟩ := relativeJoin_vertex_inl_of_projection_zero f (𝟙 Y) x hx
  let k : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ X := lift (𝟙 Δ[1]) (SSet.const y)
  let l := k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f
  have hk : stdSimplex.δ (1 : Fin 2) ≫ k = SSet.yonedaEquiv.symm y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 X := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [k, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, Category.assoc, lift_fst, Category.comp_id,
        SSet.comp_const, stdSimplex.δ_one_eq_const]
    · simp only [k, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, Category.assoc, lift_snd, Category.comp_id,
        SSet.comp_const, SSet.yonedaEquiv_symm_zero]
  refine ⟨l, ?_, ?_, ?_⟩
  · change (stdSimplex.δ 1 ≫ k) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f = SSet.yonedaEquiv.symm x
    rw [hk, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_zero, SSet.yonedaEquiv_symm_comp, hy]
  · change k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y) = 𝟙 Δ[1]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_projection]
    exact lift_fst _ _
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f) y)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_vertical_isCocartesian f y

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.3.3.3" (partial := special) "仮定：写像円筒と区間上で圏同値な準圏の模型（Lean が強い：準圏間の写像に対する標準の相対結合を選ぶ）。結論：同じ区間への射影が余デカルトファイブレーション（一致する場合。任意の模型への移送は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection_cocartesianFibration
