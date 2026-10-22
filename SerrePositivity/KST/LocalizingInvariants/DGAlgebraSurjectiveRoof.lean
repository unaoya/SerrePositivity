module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.MonoidPullbackUniversal
public import SerrePositivity.KST.LocalizingInvariants.CochainPullbackQuasiIso

/-!
概要：次数全射準同型を分母とする元の dg 代数の実 span と、その合成を構成する。
方針：元の二つの脚を保ち、合成は次数全射準同型の通常 pullback を使う。
規約：局所化の任意の射の分数表示は仮定しない。使われ方：構成済みの逆の実 roof。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

structure SurjectiveRoof (A B : Mon (Complex R)) where
  apex : Mon (Complex R)
  denominator : apex ⟶ A
  numerator : apex ⟶ B
  denominator_epi : Epi denominator.hom
  denominator_quasiIso : QuasiIso denominator.hom

namespace SurjectiveRoof
variable {A B C : Mon (Complex R)}

def ofHom (f : A ⟶ B) : SurjectiveRoof R A B where
  apex := A
  denominator := 𝟙 A
  numerator := f
  denominator_epi := by change Epi (𝟙 A.X); infer_instance
  denominator_quasiIso := by change QuasiIso (𝟙 A.X); infer_instance

variable (r : SurjectiveRoof R A B)

def postcompose (b : B ⟶ C) : SurjectiveRoof R A C where
  apex := r.apex
  denominator := r.denominator
  numerator := r.numerator ≫ b
  denominator_epi := r.denominator_epi
  denominator_quasiIso := r.denominator_quasiIso

lemma apex_isConnective (hA : IsConnective R A) : IsConnective R r.apex :=
  (quasiIso_isConnective_iff R r.denominator r.denominator_quasiIso).2 hA

variable (s : SurjectiveRoof R B C)

def comp : SurjectiveRoof R A C where
  apex := MonoidPullback.obj r.numerator s.denominator
  denominator := MonoidPullback.fst r.numerator s.denominator ≫ r.denominator
  numerator := MonoidPullback.snd r.numerator s.denominator ≫ s.numerator
  denominator_epi := by
    have := s.denominator_epi
    have h : Epi (MonoidPullback.fst r.numerator s.denominator).hom :=
      cochainPullback_fst_epi r.numerator.hom s.denominator.hom
    have := r.denominator_epi
    change Epi ((MonoidPullback.fst r.numerator s.denominator).hom ≫ r.denominator.hom)
    infer_instance
  denominator_quasiIso := by
    have := s.denominator_epi
    have h : QuasiIso (MonoidPullback.fst r.numerator s.denominator).hom :=
      cochainPullback_fst_quasiIso r.numerator.hom s.denominator.hom s.denominator_quasiIso
    change QuasiIso ((MonoidPullback.fst r.numerator s.denominator).hom ≫ r.denominator.hom)
    exact quasiIso_comp _ _ (hφ := h) (hφ' := r.denominator_quasiIso)

end SurjectiveRoof
end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
