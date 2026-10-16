module
public import SerrePositivity.DifferentialGraded.Tensor.UnitMapNaturality

/-! # 閉零bimodule圏における単位合成関手と単位自然同型 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 対角Bを前に合成する関手。 -/
def leftUnitFunctor : BimoduleCategory A B C ⥤ BimoduleCategory A B C :=
  (((Functor.const (BimoduleCategory A B C)).obj
      (BimoduleCategory.of A B B (Bimodule.diagonal A B))).prod'
    (𝟭 (BimoduleCategory A B C))) ⋙ composeFunctor A B B C

/-- 全Hom自然な閉零bimodule圏における左単位自然同型。 -/
def leftUnitNatIso : leftUnitFunctor A B C ≅ 𝟭 (BimoduleCategory A B C) :=
  NatIso.ofComponents
    (fun P => leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P))
    (fun f => leftBimoduleUnitIso_naturality A B C f)

@[simp]
lemma leftUnitNatIso_app (P : BimoduleCategory A B C) :
    (leftUnitNatIso A B C).app P =
      leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P) := rfl

variable [Small.{u} C]

/-- 対角Cを後に合成する関手。 -/
def rightUnitFunctor : BimoduleCategory A B C ⥤ BimoduleCategory A B C :=
  ((𝟭 (BimoduleCategory A B C)).prod'
    ((Functor.const (BimoduleCategory A B C)).obj
      (BimoduleCategory.of A C C (Bimodule.diagonal A C)))) ⋙ composeFunctor A B C C

/-- 全Hom自然な閉零bimodule圏における右単位自然同型。 -/
def rightUnitNatIso : rightUnitFunctor A B C ≅ 𝟭 (BimoduleCategory A B C) :=
  NatIso.ofComponents
    (fun P => rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P))
    (fun f => rightBimoduleUnitIso_naturality A B C f)

@[simp]
lemma rightUnitNatIso_app (P : BimoduleCategory A B C) :
    (rightUnitNatIso A B C).app P =
      rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P) := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
