module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleBasic
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleQuasiIso

/-! # 固定した右相対K-flat因子との合成の局所化への降下 -/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 後のbimodule Qを固定した合成関手。 -/
def composeWith (Q : BimoduleCategory A C E) :
    BimoduleCategory A B C ⥤ BimoduleCategory A B E :=
  ((𝟭 (BimoduleCategory A B C)).prod'
    ((Functor.const (BimoduleCategory A B C)).obj Q)) ⋙ composeFunctor A B C E

lemma composeWith_preserves_quasiIso (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    BimoduleCategory.quasiIso A B C ≤ (BimoduleCategory.quasiIso A B E).inverseImage
      (composeWith A B C E Q) :=
  fun _ _ f hf => composeMap_first_quasiIso A B C E Q hQ f hf

lemma composeWith_toDerived_inverts (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    (BimoduleCategory.quasiIso A B C).IsInvertedBy
      (composeWith A B C E Q ⋙ bimoduleToDerived A B E) :=
  fun _ _ f hf => bimoduleToDerived_inverts A B E _
    (composeMap_first_quasiIso A B C E Q hQ f hf)

/-- Qの右制限の相対K-flat性により、前の変数を実際の導来bimodule圏へ降ろす。 -/
def derivedComposeWith (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E :=
  bimoduleDerivedLift A B C (composeWith A B C E Q ⋙ bimoduleToDerived A B E)
    (composeWith_toDerived_inverts A B C E Q hQ)

lemma derivedComposeWith_fac (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    bimoduleToDerived A B C ⋙ derivedComposeWith A B C E Q hQ =
      composeWith A B C E Q ⋙ bimoduleToDerived A B E :=
  bimoduleDerivedLift_fac A B C _ _

instance derivedComposeWith_lifting (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    Localization.Lifting (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (composeWith A B C E Q ⋙ bimoduleToDerived A B E) (derivedComposeWith A B C E Q hQ) :=
  ⟨eqToIso (derivedComposeWith_fac A B C E Q hQ)⟩

/-- 局所化前の対象での合成の計算同型。 -/
def derivedComposeWithComputation (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (P : BimoduleCategory A B C) :
    (derivedComposeWith A B C E Q hQ).obj ((bimoduleToDerived A B C).obj P) ≅
      (bimoduleToDerived A B E).obj ((composeWith A B C E Q).obj P) :=
  (eqToIso (derivedComposeWith_fac A B C E Q hQ)).app P

lemma derivedComposeWith_unique (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (G : DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E)
    (hG : bimoduleToDerived A B C ⋙ G = composeWith A B C E Q ⋙ bimoduleToDerived A B E) :
    G = derivedComposeWith A B C E Q hQ :=
  bimoduleDerivedLift_unique A B C G _ (hG.trans (derivedComposeWith_fac A B C E Q hQ).symm)

end SerrePositivity.DifferentialGraded.BimoduleTensor
