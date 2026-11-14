module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LeftPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath

/-!
概要：left fibration の相対的な辺の始点評価。
方針：閉構造で境界の持ち上げを prism の持ち上げへ移す。
規約：辺そのものを固定するため、底の辺と始点を引き戻しに保持する。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、left fibration の transport 関手の準備。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 概要：底の辺と、その始点の上にある全空間の頂点のパラメーター空間。
方針：底の辺の始点評価と p を引き戻す。
規約：第一射影が全空間の頂点、第二射影が底の辺の族。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS） の始点を指定した相対評価。 -/
noncomputable def relativeEdgeSourceTarget {X B : SSet.{u}} (p : X ⟶ B) : SSet.{u} :=
  pullback p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))

/-- 概要：全空間の辺から、その始点と底の辺を取る。
方針：始点評価と内部 Hom の後合成を引き戻しに束ねる。
規約：端点の番号は零。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、left fibration の lift の選択。 -/
noncomputable def relativeEdgeSource {X B : SSet.{u}} (p : X ⟶ B) :
    (ihom (Δ[1] : SSet.{u})).obj X ⟶ relativeEdgeSourceTarget p :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    ((ihom (Δ[1] : SSet.{u})).map p) (by rfl)

/-- 概要：left fibration の相対的な始点評価は trivial Kan fibration。
方針：全次元の境界の持ち上げを、境界と始点を固定した prism の持ち上げに移す。
規約：底や全空間の quasicategory 性は不要。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport の存在と選択空間の可縮性。 -/
instance relativeEdgeSource_trivialKanFibration {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (relativeEdgeSource p) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  let ev₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  let r := pullback.fst p ev₀
  let s := pullback.snd p ev₀
  let H := uncurry a
  let bH := uncurry (b ≫ s)
  have h₀ : (boundary n).ι ≫ (b ≫ r) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary n : SSet.{u}) ≫ H := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    have hh := congrArg (fun f ↦ f ≫ r) sq.w
    simpa only [relativeEdgeSource, r, ev₀, Category.assoc, pullback.lift_fst] using hh.symm
  have hH : H ≫ p = (Δ[1] ◁ (boundary n).ι) ≫ bH := by
    apply curry_injective
    rw [curry_natural_right, curry_uncurry, curry_natural_left, curry_uncurry]
    have hh := congrArg (fun f ↦ f ≫ s) sq.w
    simpa only [relativeEdgeSource, s, ev₀, Category.assoc, pullback.lift_snd] using hh
  have hb : (b ≫ r) ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n] ≫ bH := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    dsimp only [r, s, ev₀]
    rw [Category.assoc, pullback.condition, Category.assoc]
  obtain ⟨F, hF, hF₀, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.leftFibration_lift_boundary_prism p n H (b ≫ r) bH h₀ hH hb
  refine CommSq.HasLift.mk' {
    l := curry F
    fac_left := ?_
    fac_right := ?_ }
  · rw [← curry_natural_left, hF, curry_uncurry]
  · apply pullback.hom_ext
    · change curry F ≫ relativeEdgeSource p ≫ r = b ≫ r
      simpa only [relativeEdgeSource, relativeEdgeSourceTarget, r, ev₀,
        Category.assoc, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval] using hF₀
    · change curry F ≫ relativeEdgeSource p ≫ s = b ≫ s
      have hh : curry F ≫ (ihom (Δ[1] : SSet.{u})).map p = b ≫ s := by
        rw [← curry_natural_right, hFp, curry_uncurry]
      simpa only [relativeEdgeSource, relativeEdgeSourceTarget, s, ev₀,
        Category.assoc, pullback.lift_snd] using hh

/-- 概要：left fibration は任意のパラメーターを持つ prism を始点から持ち上げる。
方針：相対始点評価の単射に対する rlp を空部分複体に適用する。
規約：始点の図式と底の全 prism は厳密に固定する。
使われ方：Kerodon Lemma 5.2.2.13（Tag 02RB） の left fibration 版、transport 関手の存在。 -/
lemma leftFibration_lift_prism {A X B : SSet.{u}} (p : X ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (F₀ : A ⟶ X) (b : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (hb : F₀ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ b) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ A ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ F = F₀ ∧ F ≫ p = b := by
  let ev₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  let c : A ⟶ relativeEdgeSourceTarget p :=
    pullback.lift F₀ (curry b) (hb.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval b 0).symm)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := relativeEdgeSource p) (⊥ : A.Subcomplex).ι
    inferInstance
  have sq : CommSq (Subcomplex.isInitialBot.to ((ihom (Δ[1] : SSet.{u})).obj X))
      (⊥ : A.Subcomplex).ι (relativeEdgeSource p) c :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  let F := uncurry sq.lift
  refine ⟨F, ?_, ?_⟩
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    have h := congrArg (fun f ↦ f ≫ pullback.fst p ev₀) sq.fac_right
    simpa only [relativeEdgeSource, relativeEdgeSourceTarget, c, ev₀, Category.assoc,
      pullback.lift_fst] using h
  · apply curry_injective
    rw [curry_natural_right, curry_uncurry]
    have h := congrArg (fun f ↦ f ≫ pullback.snd p ev₀) sq.fac_right
    simpa only [relativeEdgeSource, relativeEdgeSourceTarget, c, ev₀, Category.assoc,
      pullback.lift_snd] using h

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.1.2.10" (partial := direction) "仮定：左ファイブレーション p（元の iff の順方向の仮定と一致）。結論：指定 interval source の relativeEdgeSource p が TrivialKanFibration となるので順方向に一致。逆向きはない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource_trivialKanFibration
