module

public import SerrePositivity.KST.DerivedGeometry.SheafificationLocalExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Zero

/-!
概要：アーベル群前層の局所完全性から実際の層化後の完全性を得る。
方針：局所零コホモロジーの層化の消滅を完全な層化関手の比較で移す。
規約：環層上の加群を基礎アーベル群へ忘れた場合にも適用する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の自由 Čech の局所計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits ZeroObject TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable {X : TopCat.{u}}

/--
概要：各切断が局所的に零になる加群前層の層化は零。
方針：零前層からの射は局所単射で、局所消滅から局所全射となる。
規約：局所消滅の近傍と制限写像を入力に明示する。
使われ方：TT §3、Toën §3.2 の局所 Čech 収縮を層の完全性へ移す。
-/
lemma abSheafification_isZero_of_locallyZero
    (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hloc : ∀ (U : Opens X) (z : P.obj (.op U)) (x : X), x ∈ U →
      ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧ P.map (homOfLE hVU).op z = 0) :
    IsZero ((presheafToSheaf (Opens.grothendieckTopology X) (AddCommGrpCat.{u})).obj P) := by
  let τ : (0 : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⟶ P := 0
  have (U : (Opens X)ᵒᵖ) : Subsingleton ((0 : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}).obj U) :=
    AddCommGrpCat.subsingleton_of_isZero
      (Functor.map_isZero ((evaluation _ _).obj U) (isZero_zero _))
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) τ :=
    Presheaf.isLocallyInjective_of_injective _ τ (fun _ => Function.injective_of_subsingleton _)
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) τ := by
    apply (TopCat.Presheaf.isLocallySurjective_iff τ).mpr
    intro U z x hx
    obtain ⟨V, hVU, hxV, hz⟩ := hloc U z x hx
    refine ⟨V, hVU, ⟨0, ?_⟩, hxV⟩
    change (0 : P.obj (.op V)) = P.map (homOfLE hVU).op z
    exact hz.symm
  have hw := (Opens.grothendieckTopology X).W_of_isLocallyBijective τ
  have hi : IsIso ((presheafToSheaf _ _).map τ) :=
    ((Opens.grothendieckTopology X).W_iff τ).mp hw
  exact (Functor.map_isZero (presheafToSheaf _ _) (isZero_zero _)).of_iso
    (asIso ((presheafToSheaf _ _).map τ)).symm

/--
概要：短複体のコホモロジー前層が局所的に零なら層化後に完全。
方針：層化のコホモロジー比較を通して局所零前層の層化の消滅を移す。
規約：切断の大域完全性は仮定しない。
使われ方：TT §3、Toën §3.2 の局所収縮から層の完全性への移送。
-/
lemma abSheafification_exact_of_localHomologyZero
    (S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}))
    (hloc : ∀ (U : Opens X) (z : S.homology.obj (.op U)) (x : X), x ∈ U →
      ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧ S.homology.map (homOfLE hVU).op z = 0) :
    (S.map (presheafToSheaf (Opens.grothendieckTopology X) (AddCommGrpCat.{u}))).Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  exact (abSheafification_isZero_of_locallyZero S.homology hloc).of_iso
    (S.mapHomologyIso (presheafToSheaf _ _))

/--
概要：複体の指定次数のコホモロジー前層が局所的に零なら層化後はその次数で完全。
方針：同じ次数の短複体へ証明済みの局所消滅判定を適用する。
規約：任意の添字と複体形状で述べる。
使われ方：TT §3、Toën §3.2 の Čech 鎖複体と非有界の局所判定。
-/
lemma abSheafification_exactAt_of_localHomologyZero {ι : Type v} {c : ComplexShape ι}
    (K : HomologicalComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) c) (n : ι)
    (hloc : ∀ (U : Opens X) (z : (K.homology n).obj (.op U)) (x : X), x ∈ U →
      ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        (K.homology n).map (homOfLE hVU).op z = 0) :
    (((presheafToSheaf (Opens.grothendieckTopology X) (AddCommGrpCat.{u})).mapHomologicalComplex c).obj
      K).ExactAt n :=
  abSheafification_exact_of_localHomologyZero (K.sc n) hloc

/--
概要：各点で十分小さい開上の複体が完全なら層化後も完全。
方針：評価のコホモロジー比較で各類の局所消滅を示し、層化の判定へ渡す。
規約：複体の形状と有界性に制限を加えない。
使われ方：TT §3、Toën §3.2 の局所 Čech 収縮の移送。
-/
lemma abSheafification_exactAt_of_locally_exactAt {ι : Type v} {c : ComplexShape ι}
    (K : HomologicalComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) c) (n : ι)
    (hloc : ∀ (U : Opens X) (x : X), x ∈ U →
      ∃ (V : Opens X) (_ : V ≤ U), x ∈ V ∧
        ((((evaluation _ (AddCommGrpCat.{u})).obj (.op V)).mapHomologicalComplex c).obj K).ExactAt n) :
    (((presheafToSheaf (Opens.grothendieckTopology X) (AddCommGrpCat.{u})).mapHomologicalComplex c).obj
      K).ExactAt n := by
  apply abSheafification_exactAt_of_localHomologyZero K n
  intro U z x hx
  obtain ⟨V, hVU, hxV, he⟩ := hloc U x hx
  refine ⟨V, hVU, hxV, ?_⟩
  let E := (evaluation ((Opens X)ᵒᵖ) (AddCommGrpCat.{u})).obj (.op V)
  have ht : ((K.sc n).map E).Exact := he
  have hz : IsZero ((K.homology n).obj (.op V)) :=
    ((ShortComplex.exact_iff_isZero_homology _).mp ht).of_iso
      ((K.sc n).mapHomologyIso E).symm
  let := AddCommGrpCat.subsingleton_of_isZero hz
  exact Subsingleton.elim _ _


end SerrePositivity.KST.DerivedGeometry
