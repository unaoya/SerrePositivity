module
public import SerrePositivity.DifferentialGraded.Endomorphism.CoproductHomComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.CompactHomDetectsIso
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectTensor
public import SerrePositivity.DifferentialGraded.Perfect.PerfectCompact

/-! # perfectな指定対象に対する導来Homの余積保存

compact⇒Perfは外部から明示して受け取る。無限余積のcompact性は要求しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (compactToPerfect : ∀ P : DerivedModuleCategory A (EndomorphismObject E.val),
  moduleCompact A (EndomorphismObject E.val) P →
    modulePerfect A (EndomorphismObject E.val) P)

include compactToPerfect
lemma perfectEndomorphismTensor_obj_compact
    {P : DerivedModuleCategory A (EndomorphismObject E.val)}
    (hP : moduleCompact A (EndomorphismObject E.val) P) :
    moduleCompact A D ((endomorphismDerivedTensor A D E.val).obj P) :=
  modulePerfectOver_compact A D
    (perfectEndomorphismTensor_obj_perfect A D S E (compactToPerfect P hP))

lemma perfectEndomorphismHom_sigmaComparison_isIso {J : Type u}
    (F : J → DerivedModuleCategory A D) :
    IsIso (sigmaComparison (endomorphismDerivedHom A D E.val E.property.1) F) := by
  apply moduleDerived_isIso_of_compact_hom_bijective A (EndomorphismObject E.val)
  intro P hP
  exact endomorphismDerivedHom_sigmaHom_bijective A D E.val E.property.1 F P hP
    (perfectEndomorphismTensor_obj_compact A D S E compactToPerfect hP)

lemma perfectEndomorphismHom_preservesCoproduct {J : Type u}
    (F : J → DerivedModuleCategory A D) :
    PreservesColimit (Discrete.functor F)
      (endomorphismDerivedHom A D E.val E.property.1) := by
  let := perfectEndomorphismHom_sigmaComparison_isIso A D S E compactToPerfect F
  exact PreservesCoproduct.of_iso_comparison _ F

end SerrePositivity.DifferentialGraded
