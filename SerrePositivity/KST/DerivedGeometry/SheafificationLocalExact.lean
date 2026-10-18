module

public import SerrePositivity.KST.DerivedGeometry.LocallyZeroSheafification
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
概要：コホモロジーの局所消滅から層化後の完全性を得る。
方針：層化の完全性によるコホモロジー比較と局所零前層の層化の消滅を使う。
規約：複体の形状や有界性に条件を加えない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の自由 Čech 鎖複体。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable {R : Type u} [Ring R] {X : TopCat.{u}}

/--
概要：短複体のコホモロジー前層が局所的に零なら層化後に完全。
方針：層化のコホモロジー比較を通して局所零前層の層化の消滅を移す。
規約：切断の大域完全性は仮定しない。
使われ方：TT §3、Toën §3.2 の局所収縮から層の完全性への移送。
-/
lemma sheafification_exact_of_localHomologyZero
    (S : ShortComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R))
    (hloc : ∀ (U : Opens X) (z : S.homology.obj (.op U)) (x : X), x ∈ U →
      ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧ S.homology.map (homOfLE hVU).op z = 0) :
    (S.map (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))).Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  exact (sheafification_isZero_of_locallyZero S.homology hloc).of_iso
    (S.mapHomologyIso (presheafToSheaf _ _))

/--
概要：複体の指定次数のコホモロジー前層が局所的に零なら層化後はその次数で完全。
方針：同じ次数の短複体へ証明済みの局所消滅判定を適用する。
規約：任意の添字と複体形状で述べる。
使われ方：TT §3、Toën §3.2 の Čech 鎖複体と非有界の局所判定。
-/
lemma sheafification_exactAt_of_localHomologyZero {ι : Type v} {c : ComplexShape ι}
    (K : HomologicalComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) c) (n : ι)
    (hloc : ∀ (U : Opens X) (z : (K.homology n).obj (.op U)) (x : X), x ∈ U →
      ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        (K.homology n).map (homOfLE hVU).op z = 0) :
    (((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex c).obj
      K).ExactAt n :=
  sheafification_exact_of_localHomologyZero (K.sc n) hloc

/--
概要：各点で十分小さい開上の複体が完全なら層化後も完全。
方針：評価のコホモロジー比較で各類の局所消滅を示し、層化の判定へ渡す。
規約：複体の形状と有界性に制限を加えない。
使われ方：TT §3、Toën §3.2 の局所 Čech 収縮の移送。
-/
lemma sheafification_exactAt_of_locally_exactAt {ι : Type v} {c : ComplexShape ι}
    (K : HomologicalComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) c) (n : ι)
    (hloc : ∀ (U : Opens X) (x : X), x ∈ U →
      ∃ (V : Opens X) (_ : V ≤ U), x ∈ V ∧
        ((((evaluation _ (ModuleCat.{u} R)).obj (.op V)).mapHomologicalComplex c).obj K).ExactAt n) :
    (((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex c).obj
      K).ExactAt n := by
  apply sheafification_exactAt_of_localHomologyZero K n
  intro U z x hx
  obtain ⟨V, hVU, hxV, he⟩ := hloc U x hx
  refine ⟨V, hVU, hxV, ?_⟩
  let E := (evaluation ((Opens X)ᵒᵖ) (ModuleCat.{u} R)).obj (.op V)
  have ht : ((K.sc n).map E).Exact := he
  have hz : IsZero ((K.homology n).obj (.op V)) :=
    ((ShortComplex.exact_iff_isZero_homology _).mp ht).of_iso
      ((K.sc n).mapHomologyIso E).symm
  let := ModuleCat.subsingleton_of_isZero hz
  exact Subsingleton.elim _ _

end SerrePositivity.KST.DerivedGeometry
