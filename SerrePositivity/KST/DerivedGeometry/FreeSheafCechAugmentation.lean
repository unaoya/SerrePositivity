module

public import SerrePositivity.KST.DerivedGeometry.FreeSheafCech
public import SerrePositivity.KST.DerivedGeometry.AugmentedAlternatingFace

/-!
概要：開被覆の自由層による増大 Čech 鎖複体の全次数の完全性。
方針：各点の被覆元内での追加退化を増大鎖複体へ移し、層化で大域化する。
規約：零次数の全射性を含め、切断の大域完全性を仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の injective Čech 計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable (R : Type u) [Ring R] (X : TopCat.{u})
  {ι : Type u} (U : ι → Opens X) (V : Opens X) (hU : ∀ i, U i ≤ V)

/--
概要：自由前層の Čech に増大先を第0項として挿入した鎖複体。
方針：標準の増大交代面鎖複体の構成を適用する。
規約：第0項は自由前層の V に対応する一元余積。
使われ方：TT §3・§8、Toën §3.2 の増大 Čech。
-/
def freePresheafAugmentedCechComplex : ChainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) ℕ :=
  augmentedAlternatingFaceComplex (freePresheafCechAugmented R X U V hU)

/--
概要：被覆元内の開で評価すると自由前層の増大 Čech は全次数で完全。
方針：評価と増大鎖複体の比較を介して追加退化による収縮を使う。
規約：零次数・第1次数を省略しない。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech の局所完全性。
-/
lemma freePresheafAugmentedCech_evaluated_exactAt (W : Opens X) (j : ι)
    (hWj : W ≤ U j) (n : ℕ) :
    ((((evaluation _ (ModuleCat.{u} R)).obj (.op W)).mapHomologicalComplex (.down ℕ)).obj
      (freePresheafAugmentedCechComplex R X U V hU)).ExactAt n := by
  have h := augmentedAlternatingFace_acyclic
    (freePresheafCechEvaluatedExtraDegeneracy R X U V hU W j hWj) n
  exact (exactAt_iff_of_quasiIsoAt
    (augmentedAlternatingFaceMapIso ((evaluation _ _).obj (.op W))
      (freePresheafCechAugmented R X U V hU)).hom n).mpr h

/--
概要：自由前層の増大 Čech を層化した実際の自由層の増大鎖複体。
方針：完全な層化関手を全次数へ適用する。
規約：元の増大と交代面微分を保持する。
使われ方：TT §3・§8、Toën §3.2 の自由層の分解。
-/
def freeSheafAugmentedCechComplex :
    ChainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ :=
  ((presheafToSheaf _ _).mapHomologicalComplex (.down ℕ)).obj
    (freePresheafAugmentedCechComplex R X U V hU)

/--
概要：全体を被覆する族の自由層の増大 Čech 鎖複体は全次数で完全。
方針：各点を含む被覆元での全次数の収縮と層化の局所完全性判定を使う。
規約：被覆の有限性・係数の平坦性や可換性は不要。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の injective Čech 非輪状性。
-/
lemma freeSheafAugmentedCech_acyclic (hcover : (⨆ i, U i) = ⊤) :
    (freeSheafAugmentedCechComplex R X U V hU).Acyclic := by
  intro n
  apply sheafification_exactAt_of_locally_exactAt
    (freePresheafAugmentedCechComplex R X U V hU) n
  intro W x hx
  have hxc : x ∈ (⨆ i, U i) := by rw [hcover]; trivial
  obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hxc
  refine ⟨W ⊓ U j, inf_le_left, ⟨hx, hxj⟩, ?_⟩
  exact freePresheafAugmentedCech_evaluated_exactAt R X U V hU
    (W ⊓ U j) j inf_le_right n

end SerrePositivity.KST.DerivedGeometry
