module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamilyNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodynePushoutProduct
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint

/-!
概要：同じ始点と底の区間族を持つ全ての lift prism の空間。
方針：相対内部 Hom の始点制限の引き戻しを用いる。
規約：指定した輸送族は始点と底を指定するだけで、全空間の lift は固定しない。
使われ方：Kerodon Lemma 5.6.9.1（Tag 02SN） の中間空間と終点評価。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：prism の始点包含は left anodyne。
方針：零単体を補った最初の頂点包含の直積から同型を消去する。
規約：係数 K は任意。
使われ方：始点と底を固定した相対内部 Hom の trivial Kan fibration 性。 -/
lemma prismEndpoint_zero_leftAnodyne (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismFirstVertex_leftAnodyne 1 K
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.cancel_left_of_respectsIso (snd (Δ[0] : SSet.{u}) K)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex 1 0 K)).mp h

/-- 概要：prism の始点と底を同時に取る相対内部 Hom の比較。
方針：始点包含と射影 p の相対内部 Hom を標準引き戻しで構成する。
規約：定義段階で fibration 性を要求しない。
使われ方：全 lift prism の空間の周囲の射。 -/
def transportPrismRelativeHom {E B : SSet.{u}} (p : E ⟶ B) (K : SSet.{u}) :
    internalHom.PullbackObjObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K) p :=
  Functor.PullbackObjObj.ofHasPullback internalHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K) p

/-- 概要：輸送族の prism を係数を含む定義域全体に関して curry する。
方針：直積の結合子で区間と係数を先にまとめる。
規約：パラメーター L は最後の因子。
使われ方：相対内部 Hom の固定するデータを指定する射。 -/
def FiberTransportFamily.prismCurry {E B K L : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) : L ⟶ (ihom (Δ[1] ⊗ K)).obj E :=
  curry ((α_ Δ[1] K L).hom ≫ T.prism)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily (prismCurry)


/-- 概要：同じ始点と底を持つ全ての prism のパラメーター付き空間。
方針：相対内部 Hom の比較を、指定した族の始点と底の射へ引き戻す。
規約：元の族の prism 全体を固定する引き戻しではない。
使われ方：区間上の表現の境界制限の中間空間。 -/
def FiberTransportFamily.liftSpace {E B K L : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) : SSet.{u} :=
  pullback (transportPrismRelativeHom p K).π (T.prismCurry ≫ (transportPrismRelativeHom p K).π)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily (liftSpace)


/-- 概要：lift prism の空間から元のパラメーター空間への射影。
方針：相対内部 Hom の引き戻しの第二射影を取る。
規約：始点と底の区間族を同時に保持する。
使われ方：標準族の終点作用との比較の底の射。 -/
def FiberTransportFamily.liftSpaceProjection {E B K L : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) : T.liftSpace ⟶ L :=
  pullback.snd _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily (liftSpaceProjection)


/-- 概要：lift prism の空間から全ての prism の関手空間への射。
方針：引き戻しの第一射影を取る。
規約：始点と底の条件を忘れる包含。
使われ方：普遍的な lift prism の構成。 -/
def FiberTransportFamily.liftSpaceCurry {E B K L : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) : T.liftSpace ⟶ (ihom (Δ[1] ⊗ K)).obj E :=
  pullback.fst _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily (liftSpaceCurry)


/-- 概要：普遍 lift prism の始点制限は元の族の始点制限。
方針：引き戻し条件の後で相対内部 Hom の第一射影を取る。
規約：全ての高次パラメーターでの等式。
使われ方：普遍 lift prism の始点条件。 -/
lemma FiberTransportFamily.liftSpaceCurry_start {E B K L : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) :
    T.liftSpaceCurry ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)).app E =
      T.liftSpaceProjection ≫ T.prismCurry ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)).app E := by
  have h := congrArg (fun v ↦ v ≫ (transportPrismRelativeHom p K).fst)
    (pullback.condition (f := (transportPrismRelativeHom p K).π)
      (g := T.prismCurry ≫ (transportPrismRelativeHom p K).π))
  simpa only [Category.assoc, Functor.PullbackObjObj.π_fst, internalHom, Quiver.Hom.unop_op,
    FiberTransportFamily.liftSpace, FiberTransportFamily.liftSpaceCurry,
    FiberTransportFamily.liftSpaceProjection] using h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily (liftSpaceCurry_start)


/-- 概要：普遍 lift prism の底は元の区間族の底。
方針：引き戻し条件の後で相対内部 Hom の第二射影を取る。
規約：全空間の lift の射自体は固定しない。
使われ方：普遍 lift prism の底上の可換性。 -/
lemma FiberTransportFamily.liftSpaceCurry_base {E B K L : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) :
    T.liftSpaceCurry ≫ (ihom (Δ[1] ⊗ K)).map p =
      T.liftSpaceProjection ≫ T.prismCurry ≫ (ihom (Δ[1] ⊗ K)).map p := by
  have h := congrArg (fun v ↦ v ≫ (transportPrismRelativeHom p K).snd)
    (pullback.condition (f := (transportPrismRelativeHom p K).π)
      (g := T.prismCurry ≫ (transportPrismRelativeHom p K).π))
  simpa only [Category.assoc, Functor.PullbackObjObj.π_snd, internalHom,
    FiberTransportFamily.liftSpace, FiberTransportFamily.liftSpaceCurry,
    FiberTransportFamily.liftSpaceProjection] using h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily (liftSpaceCurry_base)


/-- 概要：全 lift prism の空間からパラメーターへの射影は trivial Kan fibration。
方針：始点包含の相対内部 Hom の全境界持ち上げを底変換する。
規約：left fibration の持ち上げだけを使い、モデル構造は用いない。
使われ方：終点評価と標準輸送の作用の同値性の比較。 -/
instance FiberTransportFamily.liftSpaceProjection_trivialKanFibration {E B K L : SSet.{u}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a b : B _⦋0⦌}
    {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration T.liftSpaceProjection := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.trivialKanFibration_relativeHom_of_leftAnodyne (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)
    (prismEndpoint_zero_leftAnodyne K) p (transportPrismRelativeHom p K)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily (liftSpaceProjection_trivialKanFibration)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
