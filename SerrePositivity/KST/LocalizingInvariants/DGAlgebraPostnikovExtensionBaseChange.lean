module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraExtensionBaseChangeKernel
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovKernel

/-!
概要：元の隣接 Postnikov 拡大を、指定された実下段射に沿って底変更する。
方針：元の隣接遷移を通常 pullback し、元の底・上段への両射影を保持する。
規約：元の下段射を各段同型と仮定しない。使われ方：二切断の roof に沿う底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)
  {P : Mon (Complex R)} (b : P ⟶ postnikov R B n)

def postnikovExtensionBaseChange : Mon (Complex R) :=
  ExtensionBaseChange.algebra R b (postnikovTransition R B (n + 1) n (by omega))

def postnikovExtensionBaseChangeBase : postnikovExtensionBaseChange R B n b ⟶ P :=
  ExtensionBaseChange.base R b _

def postnikovExtensionBaseChangeUpper :
    postnikovExtensionBaseChange R B n b ⟶ postnikov R B (n + 1) :=
  ExtensionBaseChange.upper R b _

lemma postnikovExtensionBaseChange_condition :
    postnikovExtensionBaseChangeBase R B n b ≫ b =
      postnikovExtensionBaseChangeUpper R B n b ≫
        postnikovTransition R B (n + 1) n (by omega) := ExtensionBaseChange.condition R b _

lemma postnikovExtensionBaseChangeBase_epi : Epi (postnikovExtensionBaseChangeBase R B n b).hom :=
  ExtensionBaseChange.base_epi R b _

lemma postnikovExtensionBaseChangeBase_surjective (j : ℤ) :
    Function.Surjective ((postnikovExtensionBaseChangeBase R B n b).hom.f j) :=
  ExtensionBaseChange.base_surjective R b _ j

lemma postnikovExtensionBaseChangeUpper_epi [Epi b.hom] :
    Epi (postnikovExtensionBaseChangeUpper R B n b).hom := ExtensionBaseChange.upper_epi R b _

lemma postnikovExtensionBaseChangeUpper_quasiIso [Epi b.hom] (hb : QuasiIso b.hom) :
    QuasiIso (postnikovExtensionBaseChangeUpper R B n b).hom :=
  ExtensionBaseChange.upper_quasiIso R b _ hb

lemma postnikovExtensionBaseChange_nonpositive [P.X.IsStrictlyLE 0] :
    (postnikovExtensionBaseChange R B n b).X.IsStrictlyLE 0 := by
  have : (postnikov R B (n + 1)).X.IsStrictlyLE 0 := postnikovComplex_nonpositive R B (n + 1)
  exact ExtensionBaseChange.nonpositive R b _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
