module
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleLocalization
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionMaps

/-! # 外側の左dg作用を制限しても右相対K-flat性を保つ -/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (E : Type w) [DGCategory A E] (D : Type z) [DGCategory A D] (F : DGFunctor A D E)

/-- 外側の左作用の制限は、各右加群を再選択するので右相対K-flat性を保つ。 -/
lemma leftRestriction_rightRelativeKFlat (Q : Bimodule A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E Q) :
    Bimodule.rightRelativeKFlat A C D (Bimodule.leftRestriction A C E D F Q) :=
  fun d => hQ (F.obj d)

lemma leftRestriction_quasiIso {Q Q' : BimoduleCategory A C E} (q : Q ⟶ Q')
    (hq : BimoduleCategory.quasiIso A C E q) :
    BimoduleCategory.quasiIso A C D
      ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map q) :=
  fun c d => hq c (F.obj d)

/-- 右K-flat部分圏上の、外側の左作用の実際の制限関手。 -/
def rightKFlatLeftRestriction :
    RightKFlatBimoduleCategory A C E ⥤ RightKFlatBimoduleCategory A C D where
  obj Q := ⟨(BimoduleCategory.middleLeftRestrictionFunctor A C E D F).obj Q.obj,
    leftRestriction_rightRelativeKFlat A C E D F _ Q.property⟩
  map q := ⟨(BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map q.hom⟩
  map_id Q := by apply ObjectProperty.hom_ext; rfl
  map_comp q r := by apply ObjectProperty.hom_ext; rfl

lemma rightKFlatLeftRestriction_fac :
    rightKFlatLeftRestriction A C E D F ⋙ rightKFlatInclusion A C D =
      rightKFlatInclusion A C E ⋙ BimoduleCategory.middleLeftRestrictionFunctor A C E D F := rfl

lemma rightKFlatLeftRestriction_quasiIso
    {Q Q' : RightKFlatBimoduleCategory A C E} (q : Q ⟶ Q') (hq : rightKFlatQuasiIso A C E q) :
    rightKFlatQuasiIso A C D ((rightKFlatLeftRestriction A C E D F).map q) :=
  leftRestriction_quasiIso A C E D F q.hom hq

end SerrePositivity.DifferentialGraded.BimoduleTensor
