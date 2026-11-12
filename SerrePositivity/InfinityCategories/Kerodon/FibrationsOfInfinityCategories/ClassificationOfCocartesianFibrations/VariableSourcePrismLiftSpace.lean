module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace

/-!
概要：初期値もパラメーターとともに動く全 lift prism の空間。
方針：相対内部 Hom の始点・底データへの任意の射に沿って引き戻す。
規約：初期値 K⊗L→E は L に依存してよい。
使われ方：Kerodon Lemma 5.6.9.1（Tag 02SN） の始点同値の空間全体での組み立て。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：動く初期値と底の prism を相対内部 Hom のデータへ束ねる。
方針：二つの射を curry し、初期値の底の可換性を使う。
規約：v は係数 K とパラメーター L の両方に依存してよい。
使われ方：始点の同値も動かす lift prism 空間の定義。 -/
def prismLiftData {E B K L : SSet.{u}} (p : E ⟶ B) (v : K ⊗ L ⟶ E)
    (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B) (hv : v ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ) :
    L ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).pt := by
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).isPullback.lift (curry v)
    (curry ((α_ Δ[1] K L).hom ≫ δ)) ?_
  change curry v ≫ (ihom K).map p =
    curry ((α_ Δ[1] K L).hom ≫ δ) ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)).app B
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_pre_app, uncurry_curry, uncurry_curry]
  exact hv

/-- 概要：動く初期値のデータの第一成分はその curry。
方針：相対内部 Hom の引き戻しの第一射影を使う。
規約：初期値は全パラメーターに依存してよい。
使われ方：普遍 lift prism の始点の確認。 -/
lemma prismLiftData_fst {E B K L : SSet.{u}} (p : E ⟶ B) (v : K ⊗ L ⟶ E)
    (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B) (hv : v ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ) :
    prismLiftData p v δ hv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).fst = curry v :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).isPullback.lift_fst _ _ _

/-- 概要：動く初期値のデータの第二成分は底の prism の curry。
方針：相対内部 Hom の引き戻しの第二射影を使う。
規約：区間と係数を先にまとめる。
使われ方：普遍 lift prism の底の確認。 -/
lemma prismLiftData_snd {E B K L : SSet.{u}} (p : E ⟶ B) (v : K ⊗ L ⟶ E)
    (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B) (hv : v ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ) :
    prismLiftData p v δ hv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).snd =
      curry ((α_ Δ[1] K L).hom ≫ δ) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).isPullback.lift_snd _ _ _

/-- 概要：始点・底データの族に依存する全 lift prism の空間。
方針：相対内部 Hom の始点制限をデータの族へ引き戻す。
規約：選択した lift prism の存在は定義に要求しない。
使われ方：動く始点同値に対する中間空間。 -/
def prismLiftSpace {E B L : SSet.{u}} (p : E ⟶ B) (K : SSet.{u})
    (d : L ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).pt) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).π d

/-- 概要：動く初期値の全 lift の空間からパラメーターへの射影。
方針：引き戻しの第二射影を取る。
規約：パラメーターは任意の単体集合。
使われ方：始点同値の空間への射と、その fiber の比較。 -/
def prismLiftSpaceProjection {E B L : SSet.{u}} (p : E ⟶ B) (K : SSet.{u})
    (d : L ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).pt) : prismLiftSpace p K d ⟶ L :=
  pullback.snd _ _

/-- 概要：動く初期値の全 lift の空間から prism の関手空間への射。
方針：引き戻しの第一射影を取る。
規約：初期値のパラメーター依存を固定値へ弱めない。
使われ方：普遍評価と終点制限の構成。 -/
def prismLiftSpaceCurry {E B L : SSet.{u}} (p : E ⟶ B) (K : SSet.{u})
    (d : L ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).pt) :
    prismLiftSpace p K d ⟶ (ihom (Δ[1] ⊗ K)).obj E :=
  pullback.fst _ _

/-- 概要：動く初期値の lift 空間のパラメーター射影は trivial Kan fibration。
方針：始点包含の相対内部 Hom の全境界持ち上げを底変換する。
規約：初期値の族やパラメーターの充填性は要求しない。
使われ方：始点同値も動く場合の lift の可縮な選択。 -/
instance prismLiftSpaceProjection_trivialKanFibration {E B L : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (K : SSet.{u})
    (d : L ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).pt) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (prismLiftSpaceProjection p K d) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.trivialKanFibration_relativeHom_of_leftAnodyne (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismEndpoint_zero_leftAnodyne K) p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

/-- 概要：実際の prism の初期値と底で作ったデータは、その prism の相対制限に一致する。
方針：相対内部 Hom の二射影で比較し、curry した初期値と底の等式を使う。
規約：全空間の射 H を指定しても、データは初期値と底だけを含む。
使われ方：固定始点の旧 lift 空間と動く初期値の空間の厳密な接続。 -/
lemma prismLiftData_eq_of_prism {E B K L : SSet.{u}} (p : E ⟶ B) (v : K ⊗ L ⟶ E)
    (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B) (hv : v ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ)
    (H : Δ[1] ⊗ (K ⊗ L) ⟶ E) (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = v) (hp : H ≫ p = δ) :
    prismLiftData p v δ hv =
      curry ((α_ Δ[1] K L).hom ≫ H) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).π := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).hom_ext
  · rw [Category.assoc, Functor.PullbackObjObj.π_fst, prismLiftData_fst]
    simp only [internalHom, Quiver.Hom.unop_op]
    change curry v = curry ((α_ Δ[1] K L).hom ≫ H) ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)).app E
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
    exact h₀.symm
  · rw [Category.assoc, Functor.PullbackObjObj.π_snd, prismLiftData_snd]
    change curry ((α_ Δ[1] K L).hom ≫ δ) =
      curry ((α_ Δ[1] K L).hom ≫ H) ≫ (ihom (Δ[1] ⊗ K)).map p
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry, uncurry_curry, Category.assoc, hp]

/-- 概要：固定した初期係数射を持つ輸送族も、動く初期値のデータとして表示できる。
方針：元の輸送族の始点と底の公式から初期値の可換性を得る。
規約：初期値を定値化するのはこの特殊化だけ。
使われ方：既証明の固定始点の終点同値性の再利用。 -/
def FiberTransportFamily.liftData {E B K L : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) : L ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).pt :=
  prismLiftData p (fst K L ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a) ((Δ[1] ◁ snd K L) ≫ γ) (by
    rw [← T.start, Category.assoc, T.over_base])

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily (liftData)


/-- 概要：固定始点の輸送族のデータは元の prism の相対制限。
方針：実際の prism による一般のデータの公式を適用する。
規約：射そのものの厳密な一致。
使われ方：新旧の lift 空間を同型で結ぶ。 -/
lemma FiberTransportFamily.liftData_eq {E B K L : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) :
    T.liftData = T.prismCurry ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).π :=
  prismLiftData_eq_of_prism p _ _ _ T.prism T.start T.over_base

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily (liftData_eq)


/-- 概要：動く初期値の空間を固定始点へ特殊化すると既存の全 lift 空間と厳密に同型。
方針：始点・底データの等式を引き戻しの対象へ写す。
規約：既存の固定始点の構成を変更しない。
使われ方：fiber ごとの終点評価の同値性を新しい空間へ移す。 -/
def FiberTransportFamily.variableLiftSpaceIso {E B K L : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) : prismLiftSpace p K T.liftData ≅ T.liftSpace :=
  eqToIso (congrArg (fun d ↦ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).π d) T.liftData_eq)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily (variableLiftSpaceIso)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
