module

public import SerrePositivity.KST.DerivedGeometry.SheafLocalBoundaries
public import Mathlib.CategoryTheory.Sites.Localization

/-!
概要：局所的に零となる加群前層の層化は零対象。
方針：零前層からの射が局所全単射であることを示し、層化の同値判定を使う。
規約：局所消滅を大域切断の消滅と同一視しない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の Čech 鎖複体の局所完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits ZeroObject TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable {R : Type u} [Ring R] {X : TopCat.{u}}

/--
概要：各切断が局所的に零になる加群前層の層化は零。
方針：零前層からの射は局所単射で、局所消滅から局所全射となる。
規約：局所消滅の近傍と制限写像を入力に明示する。
使われ方：TT §3、Toën §3.2 の局所 Čech 収縮を層の完全性へ移す。
-/
lemma sheafification_isZero_of_locallyZero
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (hloc : ∀ (U : Opens X) (z : P.obj (.op U)) (x : X), x ∈ U →
      ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧ P.map (homOfLE hVU).op z = 0) :
    IsZero ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj P) := by
  let τ : (0 : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) ⟶ P := 0
  have (U : (Opens X)ᵒᵖ) : Subsingleton ((0 : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R).obj U) :=
    ModuleCat.subsingleton_of_isZero
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

end SerrePositivity.KST.DerivedGeometry
