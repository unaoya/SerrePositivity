module

public import SerrePositivity.KST.LocalizingInvariants.MonoidPullbackUniversal
public import SerrePositivity.KST.LocalizingInvariants.CochainPullbackQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.CochainPullbackBounds

/-!
概要：元の実 dg 代数拡大の底変更と、元の底・上段への実射影を保持する。
方針：元の二つの代数射の通常 pullback を使い、全射準同型の底変更を適用する。
規約：底への射に準同型性を仮定しない定義。使われ方：roof に沿う Postnikov 拡大。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.ExtensionBaseChange
variable (R : Type u) [CommRing R] {P U B : Mon (Complex R)} (b : P ⟶ B) (q : U ⟶ B)

def algebra : Mon (Complex R) := MonoidPullback.obj b q

def base : algebra R b q ⟶ P := MonoidPullback.fst b q

def upper : algebra R b q ⟶ U := MonoidPullback.snd b q

lemma condition : base R b q ≫ b = upper R b q ≫ q := MonoidPullback.condition b q

lemma upper_epi [Epi b.hom] : Epi (upper R b q).hom := cochainPullback_snd_epi b.hom q.hom

lemma upper_quasiIso [Epi b.hom] (hb : QuasiIso b.hom) : QuasiIso (upper R b q).hom :=
  cochainPullback_snd_quasiIso b.hom q.hom hb

lemma upper_surjective [Epi b.hom] (j : ℤ) : Function.Surjective ((upper R b q).hom.f j) :=
  cochainPullback_snd_surjective b.hom q.hom j

lemma base_epi [Epi q.hom] : Epi (base R b q).hom := cochainPullback_fst_epi b.hom q.hom

lemma base_surjective [Epi q.hom] (j : ℤ) : Function.Surjective ((base R b q).hom.f j) :=
  cochainPullback_fst_surjective b.hom q.hom j

lemma nonpositive [P.X.IsStrictlyLE 0] [U.X.IsStrictlyLE 0] :
    (algebra R b q).X.IsStrictlyLE 0 := CochainPullback.isStrictlyLE b.hom q.hom 0

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.ExtensionBaseChange
