module

public import SerrePositivity.KST.DerivedGeometry.FreePresheafCech
public import SerrePositivity.KST.DerivedGeometry.SheafificationLocalExact

/-!
概要：開被覆の自由加群層の Čech 鎖複体の正次数の完全性。
方針：被覆元に含まれる近傍での収縮を層化の局所完全性判定へ渡す。
規約：被覆の有限性や係数環の可換性・平坦性は不要。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の injective への Hom の入力。
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
概要：自由前層の Čech 鎖複体を層化して自由層の Čech 鎖複体を構成する。
方針：完全な層化関手を全次数と微分へ適用する。
規約：各項は元の自由前層の実際の層化。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech 分解。
-/
def freeSheafCechComplex :
    ChainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ :=
  ((presheafToSheaf _ _).mapHomologicalComplex (.down ℕ)).obj
    (freePresheafCechComplex R X U V hU)

/--
概要：全体を被覆する開族の自由層の Čech 鎖複体は全正次数で完全。
方針：各点を含む被覆元と試験開の交叉での局所収縮を層化後へ移す。
規約：任意の被覆・全次数で同じ交代面微分を用いる。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の自由 Čech 分解。
-/
lemma freeSheafCech_exactAt (hcover : (⨆ i, U i) = ⊤) (n : ℕ) :
    (freeSheafCechComplex R X U V hU).ExactAt (n + 1) := by
  apply sheafification_exactAt_of_locally_exactAt (freePresheafCechComplex R X U V hU) (n + 1)
  intro W x hx
  have hxc : x ∈ (⨆ i, U i) := by rw [hcover]; trivial
  obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hxc
  refine ⟨W ⊓ U j, inf_le_left, ⟨hx, hxj⟩, ?_⟩
  exact freePresheafCech_evaluated_exactAt R X U V hU (W ⊓ U j) j inf_le_right n

end SerrePositivity.KST.DerivedGeometry
