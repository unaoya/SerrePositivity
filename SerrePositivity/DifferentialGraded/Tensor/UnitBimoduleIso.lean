module
public import SerrePositivity.DifferentialGraded.Tensor.LeftUnit
public import SerrePositivity.DifferentialGraded.Bimodule.Isomorphism
public import SerrePositivity.DifferentialGraded.Bimodule.LeftEvaluation

/-! # 対角bimoduleの単位比較を全Hom自然な閉零同型として読む -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 対角Bとの合成の閉零bimodule圏での左単位同型。 -/
def leftBimoduleUnitIso (P : Bimodule A B C) :
    BimoduleCategory.of A B C (compose A B B C (Bimodule.diagonal A B) P) ≅
      BimoduleCategory.of A B C P :=
  BimoduleCategory.isoOfFamily A B C (leftUnitIso A B C P) (leftUnitIso_naturality A B C P)

@[simp]
lemma leftBimoduleUnitIso_hom_value (P : Bimodule A B C) (b : B) (c : C) :
    (BimoduleCategory.valueEvaluation A B C b c).map (leftBimoduleUnitIso A B C P).hom =
      (leftUnitValueIso A B C P b c).hom := leftUnitIso_hom_eval A B C P b c

@[simp]
lemma leftBimoduleUnitIso_inv_value (P : Bimodule A B C) (b : B) (c : C) :
    (BimoduleCategory.valueEvaluation A B C b c).map (leftBimoduleUnitIso A B C P).inv =
      (leftUnitValueIso A B C P b c).inv := leftUnitIso_inv_eval A B C P b c

variable [Small.{u} C]

/-- 対角Cとの合成の閉零bimodule圏での右単位同型。 -/
def rightBimoduleUnitIso (P : Bimodule A B C) :
    BimoduleCategory.of A B C (compose A B C C P (Bimodule.diagonal A C)) ≅
      BimoduleCategory.of A B C P :=
  BimoduleCategory.isoOfFamily A B C (rightUnitIso A B C P) (rightUnitIso_naturality A B C P)

@[simp]
lemma rightBimoduleUnitIso_hom_value (P : Bimodule A B C) (b : B) (c : C) :
    (BimoduleCategory.valueEvaluation A B C b c).map (rightBimoduleUnitIso A B C P).hom =
      (rightUnitValueIso A B C P b c).hom := rightUnitIso_hom_eval A B C P b c

@[simp]
lemma rightBimoduleUnitIso_inv_value (P : Bimodule A B C) (b : B) (c : C) :
    (BimoduleCategory.valueEvaluation A B C b c).map (rightBimoduleUnitIso A B C P).inv =
      (rightUnitValueIso A B C P b c).inv := rightUnitIso_inv_eval A B C P b c

end SerrePositivity.DifferentialGraded.BimoduleTensor
