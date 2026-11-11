module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftEvaluation

/-!
概要：始点と底を固定した全 lift prism の空間のパラメーター付き普遍性。
方針：与えられた prism を curry して相対内部 Hom の引き戻しへ戻す。
規約：元の輸送族の prism と一致することは要求せず、始点と底だけを固定する。
使われ方：固定した始点の比較を動かす族への組み立てと境界上での厳密な回収。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：同じ始点と底を持つ任意の prism 族を全 lift の空間へ戻す。
方針：始点と底の二つの等式を相対内部 Hom の二射影の一致へ curry する。
規約：パラメーターの射 g は任意。
使われ方：全 lift の空間が必要な prism の族を全て含むことの確認。 -/
def FiberTransportFamily.liftSpaceLift {E B K L M : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) (g : M ⟶ L)
    (H : Δ[1] ⊗ (K ⊗ M) ⟶ E)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ (T.precomp g).prism)
    (hp : H ≫ p = (T.precomp g).prism ≫ p) : M ⟶ T.liftSpace := by
  let v := curry ((α_ Δ[1] K M).hom ≫ H)
  refine pullback.lift v g ?_
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).hom_ext
  · simp only [Category.assoc, Functor.PullbackObjObj.π_fst]
    change v ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)).app E =
      g ≫ T.prismCurry ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)).app E
    apply uncurry_injective
    change uncurry (v ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)).app E) =
      uncurry ((g ≫ T.prismCurry) ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)).app E)
    rw [uncurry_pre_app, uncurry_pre_app]
    dsimp only [v]
    rw [uncurry_curry, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily.prismCurry, uncurry_curry]
    exact h₀
  · simp only [Category.assoc, Functor.PullbackObjObj.π_snd]
    change v ≫ (ihom (Δ[1] ⊗ K)).map p = g ≫ T.prismCurry ≫ (ihom (Δ[1] ⊗ K)).map p
    apply uncurry_injective
    change uncurry (v ≫ (ihom (Δ[1] ⊗ K)).map p) =
      uncurry ((g ≫ T.prismCurry) ≫ (ihom (Δ[1] ⊗ K)).map p)
    rw [uncurry_natural_right, uncurry_natural_right]
    dsimp only [v]
    rw [uncurry_curry, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily.prismCurry, uncurry_curry]
    exact congrArg (fun R ↦ (α_ Δ[1] K M).hom ≫ R) hp

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberTransportFamily (liftSpaceLift)


/-- 概要：prism 族を lift 空間へ戻してパラメーターを取ると元の射。
方針：引き戻しの第二射影の公式。
規約：境界上のパラメーターも厳密に保つ。
使われ方：全 lift の空間の底変換の確認。 -/
lemma FiberTransportFamily.liftSpaceLift_projection {E B K L M : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) (g : M ⟶ L)
    (H : Δ[1] ⊗ (K ⊗ M) ⟶ E)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ (T.precomp g).prism)
    (hp : H ≫ p = (T.precomp g).prism ≫ p) :
    T.liftSpaceLift g H h₀ hp ≫ T.liftSpaceProjection = g :=
  pullback.lift_snd _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberTransportFamily (liftSpaceLift_projection)


/-- 概要：全 lift の空間へ戻した prism 族を普遍評価すると元の prism。
方針：引き戻しの第一射影と curry の逆関係を使う。
規約：高次パラメーターを含む射そのものの厳密な回収。
使われ方：境界固定の延長を全 lift の空間から実際の図式へ戻す。 -/
lemma FiberTransportFamily.liftSpaceLift_prism {E B K L M : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) (g : M ⟶ L)
    (H : Δ[1] ⊗ (K ⊗ M) ⟶ E)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ (T.precomp g).prism)
    (hp : H ≫ p = (T.precomp g).prism ≫ p) :
    (Δ[1] ◁ (K ◁ T.liftSpaceLift g H h₀ hp)) ≫ T.liftSpacePrism = H := by
  have hv : T.liftSpaceLift g H h₀ hp ≫ T.liftSpaceCurry =
      curry ((α_ Δ[1] K M).hom ≫ H) := pullback.lift_fst _ _ _
  calc
    _ = (α_ Δ[1] K M).inv ≫ uncurry (T.liftSpaceLift g H h₀ hp ≫ T.liftSpaceCurry) := by
      rw [uncurry_natural_left]
      rfl
    _ = _ := by rw [hv, uncurry_curry, Iso.inv_hom_id_assoc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberTransportFamily (liftSpaceLift_prism)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
