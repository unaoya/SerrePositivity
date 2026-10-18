module

public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
概要：完全な加群層の複体におけるサイクルの局所的な境界表示。
方針：完全性からサイクルへの境界射が epi であることと局所全射性を使う。
規約：実際の層のサイクルを扱い、大域切断の完全性を仮定しない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の Čech と層コホモロジーの接続。
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
概要：加群層の完全な短複体の境界からサイクルへの射は局所全射。
方針：完全性から得た epi に層の局所全射性の判定を適用する。
規約：切断ごとの大域全射を主張しない。
使われ方：TT §3、Toën §3.2 の局所境界の表示。
-/
lemma sheafExact_toCycles_locallySurjective
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (hS : S.Exact) :
    TopCat.Presheaf.IsLocallySurjective S.toCycles.hom := by
  let : Epi S.toCycles := hS.epi_toCycles
  exact (CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
    (ModuleCat.{u} R) S.toCycles).mpr inferInstance

/--
概要：サイクル層の切断は各点の近傍で境界から持ち上がる。
方針：局所全射性を開集合と切断による具体的な存在表示へ展開する。
規約：近傍の包含と境界等式を明示する。
使われ方：TT §3、Toën §3.2 の局所コホモロジー消滅の入力。
-/
lemma sheafExact_localBoundary
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (hS : S.Exact)
    (U : Opens X) (z : S.cycles.obj.obj (.op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U),
      (∃ y : S.X₁.obj.obj (.op V),
        S.toCycles.hom.app (.op V) y =
          S.cycles.obj.map (homOfLE hVU).op z) ∧ x ∈ V := by
  exact (TopCat.Presheaf.isLocallySurjective_iff S.toCycles.hom).mp
    (sheafExact_toCycles_locallySurjective S hS) U z x hx

end SerrePositivity.KST.DerivedGeometry
