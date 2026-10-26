module
public import SerrePositivity.KST.Fibration.ClosedFlagCofiberCoordinates
public import SerrePositivity.KST.Fibration.FiniteFlagComparisonInduction

/-!
概要：閉じた安定部分圏 P の全有限旗を、初期頂点と全連続 cofiber の実有限積へ送る。
方針：元の全合成辺に共通する補完を、同じ元の順序で束ねる。
規約：商や核表示を使わず、全作用素で元の評価を回収する。
使われ方：K-B2 向け全旗帰納と初期評価四角形の共通化。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration
open Relative

/-- 概要：元の全連続辺の P cofiber を元の順序の有限積に束ねる。
方針：同じ共通補完の実現射を各射影とする。
規約：零長を含む。使われ方：有限旗の係数座標。 -/
def closedFlagConsecutiveCofibers {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n r : ℕ) : (multiRealizationFunctor r).obj (closedFlagModel P ⦋n⦌) ⟶
      ∏ᶜ fun _ : Fin n => (multiRealizationFunctor r).obj (closedStableModel P) :=
  Pi.lift (fun i => (multiRealizationFunctor r).map
    (closedFlagCofiber P (consecutiveWeakStringEdge n i)))

/-- 概要：初期頂点と全連続 cofiber の元の有限旗比較。
方針：実評価と上の実有限積座標を束ねる。
規約：同値性は相対加法性から別に証明する。
使われ方：既存 W 列と共通する帰納の実比較写像。 -/
def closedFlagFiniteComparison {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n r : ℕ) : (multiRealizationFunctor r).obj (closedFlagModel P ⦋n⦌) ⟶
      (multiRealizationFunctor r).obj B ⊗
        ∏ᶜ fun _ : Fin n => (multiRealizationFunctor r).obj (closedStableModel P) :=
  lift ((multiRealizationFunctor r).map (closedFlagVertex P ⦋n⦌ 0))
    (closedFlagConsecutiveCofibers P n r)

/-- 概要：有限比較の第一成分は同じ実初期頂点評価。
方針：積の第一射影。規約：全反復。使われ方：初期評価四角形の照合。 -/
theorem closedFlagFiniteComparison_initial {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n r : ℕ) : closedFlagFiniteComparison P n r ≫ fst _ _ =
      (multiRealizationFunctor r).map (closedFlagVertex P ⦋n⦌ 0) := lift_fst _ _

/-- 概要：各有限積成分は元の指定連続辺の同じ共通 cofiber。
方針：積の第二射影と指定因子の射影。
規約：全有限添字。使われ方：全再添字の成分計算。 -/
theorem closedFlagFiniteComparison_cofiber {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n r : ℕ) (i : Fin n) : closedFlagFiniteComparison P n r ≫ snd _ _ ≫ Pi.π _ i =
      (multiRealizationFunctor r).map (closedFlagCofiber P (consecutiveWeakStringEdge n i)) := by
  rw [closedFlagFiniteComparison, lift_snd_assoc]
  exact Pi.lift_comp_π _ _

/-- 概要：任意の制限後の初期成分は元の対応する頂点評価。
方針：実完全射の厳密再添字を実現へ送る。
規約：全ての単体作用素。使われ方：有限旗自然性の第一成分。 -/
theorem closedFlagFiniteComparison_reindex_initial {B : StableModel.{u}}
    (P : ClosedStablePredicate B) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (r : ℕ) :
    (multiRealizationFunctor r).map (closedFlagMap P θ) ≫
      closedFlagFiniteComparison P m r ≫ fst _ _ =
        (multiRealizationFunctor r).map (closedFlagVertex P ⦋n⦌ (θ.toOrderHom 0)) := by
  rw [closedFlagFiniteComparison_initial, ← Functor.map_comp, closedFlagVertex_reindex]

/-- 概要：任意の制限後の cofiber 成分は元の実合成辺の同じ補完。
方針：実 cofiber の厳密再添字を実現へ送る。
規約：退化と合成辺を保持。使われ方：有限旗自然性の全係数成分。 -/
theorem closedFlagFiniteComparison_reindex_cofiber {B : StableModel.{u}}
    (P : ClosedStablePredicate B) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (r : ℕ) (i : Fin m) :
    (multiRealizationFunctor r).map (closedFlagMap P θ) ≫
      closedFlagFiniteComparison P m r ≫ snd _ _ ≫ Pi.π _ i =
        (multiRealizationFunctor r).map
          (closedFlagCofiber P (consecutiveWeakStringEdge m i ≫ θ)) := by
  rw [closedFlagFiniteComparison_cofiber, ← Functor.map_comp, closedFlagCofiber_reindex]

end SerrePositivity.KST.Fibration
