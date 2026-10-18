module

public import SerrePositivity.KST.DerivedGeometry.SheafLocalBoundaries
public import SerrePositivity.KST.DerivedGeometry.LeftExactCycles
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory

/-!
概要：切断のサイクルを層のサイクルの切断へ持ち上げる。
方針：切断関手の左完全性と核の比較のみを使う。
規約：大域切断の右完全性を仮定しない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の局所境界とコホモロジーの接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable {R : Type u} [Ring R] {X : TopCat.{u}}

/--
概要：固定した開上の加群層の切断関手。
方針：層の包含と前層の評価関手を合成する。
規約：切断の元の R 加群構造を保持する。
使われ方：TT §3、Toën §3.2 の局所コホモロジー。
-/
def sheafModuleSections (U : Opens X) :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (.op U)

/--
概要：加群層の切断は加法的。
方針：射の加法が各開で計算されることを使う。
規約：加法性だけでは右完全性を主張しない。
使われ方：TT §3、Toën §3.2 の切断の複体。
-/
instance sheafModuleSections_additive (U : Opens X) : (sheafModuleSections (R := R) U).Additive where
  map_add := by intros; rfl

/--
概要：加群層の切断は有限極限を保つ。
方針：層の包含と前層の評価の極限保存を合成する。
規約：特に核の保存だけでサイクルを比較する。
使われ方：TT §3、Toën §3.2 の切断のサイクル。
-/
instance sheafModuleSections_preservesFiniteLimits (U : Opens X) :
    PreservesFiniteLimits (sheafModuleSections (R := R) U) := by
  dsimp [sheafModuleSections]
  infer_instance

/--
概要：微分で零となる切断はサイクル層の切断へ持ち上がる。
方針：加群のサイクルを作り、左完全な切断関手の核の比較を使う。
規約：元の層のサイクルへの実際の元を構成する。
使われ方：TT §3、Toën §3.2 の局所境界表示。
-/
def sheafSectionCycle
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (U : Opens X) (z : S.X₂.obj.obj (.op U)) (hz : S.g.hom.app (.op U) z = 0) :
    S.cycles.obj.obj (.op U) :=
  (leftExactCyclesIso (sheafModuleSections U) S).hom
    ((S.map (sheafModuleSections U)).cyclesMk z hz)

/--
概要：サイクル層への持ち上げを包含すると元の切断に戻る。
方針：核の比較の包含との両立と加群のサイクルの公式を使う。
規約：切断の元の等式を保持する。
使われ方：TT §3、Toën §3.2 の境界等式の移送。
-/
lemma sheafSectionCycle_iCycles
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (U : Opens X) (z : S.X₂.obj.obj (.op U)) (hz : S.g.hom.app (.op U) z = 0) :
    S.iCycles.hom.app (.op U) (sheafSectionCycle S U z hz) = z := by
  exact (congrArg (fun k => k ((S.map (sheafModuleSections U)).cyclesMk z hz))
    (leftExactCyclesIso_hom_iCycles (sheafModuleSections U) S)).trans
      ((S.map (sheafModuleSections U)).i_cyclesMk z hz)

/--
概要：完全な加群層の複体の任意のサイクル切断は各点の近傍で境界。
方針：サイクル層へ持ち上げ、局所全射性を使い、包含の自然性で元の等式に戻す。
規約：層の完全性だけを使い、大域切断の完全性は仮定しない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の局所コホモロジー消滅の入力。
-/
lemma sheafExact_localCocycleBoundary
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (hS : S.Exact) (U : Opens X) (z : S.X₂.obj.obj (.op U))
    (hz : S.g.hom.app (.op U) z = 0) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U),
      (∃ y : S.X₁.obj.obj (.op V), S.f.hom.app (.op V) y =
        S.X₂.obj.map (homOfLE hVU).op z) ∧ x ∈ V := by
  let c := sheafSectionCycle S U z hz
  obtain ⟨V, hVU, ⟨y, hy⟩, hxV⟩ := sheafExact_localBoundary S hS U c x hx
  refine ⟨V, hVU, ⟨y, ?_⟩, hxV⟩
  calc
    _ = S.iCycles.hom.app (.op V) (S.toCycles.hom.app (.op V) y) := by
      exact (congrArg (fun k : S.X₁ ⟶ S.X₂ => k.hom.app (.op V) y) S.toCycles_i).symm
    _ = S.iCycles.hom.app (.op V) (S.cycles.obj.map (homOfLE hVU).op c) := by rw [hy]
    _ = S.X₂.obj.map (homOfLE hVU).op (S.iCycles.hom.app (.op U) c) :=
      congrArg (fun k : S.cycles.obj.obj (.op U) ⟶ S.X₂.obj.obj (.op V) => k c)
        (S.iCycles.hom.naturality (homOfLE hVU).op)
    _ = _ := by rw [sheafSectionCycle_iCycles]

end SerrePositivity.KST.DerivedGeometry
