module
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectTensorDG
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # U13 dg enhancementの閉零圏への実際の再構成随伴の制限 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

def perfectEndomorphismTensorClosedInclusionIso :
    (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onClosed ⋙
        (endomorphismModuleTensor A D E.val).onClosed ≅
      (perfectEndomorphismTensorDG A D S E).onClosed ⋙
        (perfectDGModuleInclusion A D S).onClosed :=
  (EnrichedFunctor.forgetComp
    (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ)
    (endomorphismModuleTensor A D E.val)).symm ≪≫
    eqToIso (congrArg DGFunctor.onClosed
      (perfectEndomorphismTensorDG_inclusion_square A D S E).symm) ≪≫
    EnrichedFunctor.forgetComp (perfectEndomorphismTensorDG A D S E)
      (perfectDGModuleInclusion A D S)

variable (hgen : endomorphismThickGeneratesPerfect A D S E)

def perfectEndomorphismHomClosedInclusionIso :
    (perfectDGModuleInclusion A D S).onClosed ⋙ (endomorphismModuleHom A D E.val).onClosed ≅
      (perfectEndomorphismDG A D S E hgen).onClosed ⋙
        (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onClosed :=
  (EnrichedFunctor.forgetComp (perfectDGModuleInclusion A D S)
    (endomorphismModuleHom A D E.val)).symm ≪≫
    eqToIso (congrArg DGFunctor.onClosed
      (perfectEndomorphismDG_inclusion_square A D S E hgen).symm) ≪≫
    EnrichedFunctor.forgetComp (perfectEndomorphismDG A D S E hgen)
      (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ)

/-- 全加群上の実際の随伴を、HPかつperfectな実際のdg対象の閉零圏へ制限する。 -/
def perfectEndomorphismEnhancementAdjunction :
    (perfectEndomorphismTensorDG A D S E).onClosed ⊣
      (perfectEndomorphismDG A D S E hgen).onClosed := by
  have : (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onClosed.Full := by
    unfold perfectDGModuleInclusion
    infer_instance
  have : (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onClosed.Faithful := by
    unfold perfectDGModuleInclusion
    infer_instance
  have : (perfectDGModuleInclusion A D S).onClosed.Full := by
    unfold perfectDGModuleInclusion
    infer_instance
  have : (perfectDGModuleInclusion A D S).onClosed.Faithful := by
    unfold perfectDGModuleInclusion
    infer_instance
  exact (endomorphismModuleAdjunction A D E.val).restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful
      (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onClosed)
    (Functor.FullyFaithful.ofFullyFaithful (perfectDGModuleInclusion A D S).onClosed)
    (perfectEndomorphismTensorClosedInclusionIso A D S E)
    (perfectEndomorphismHomClosedInclusionIso A D S E hgen)

lemma perfectEndomorphismEnhancement_left_triangle
    (N : ClosedCategory A (PerfectDGModule A (EndomorphismObject E.val))) :
    (perfectEndomorphismTensorDG A D S E).onClosed.map
        ((perfectEndomorphismEnhancementAdjunction A D S E hgen).unit.app N) ≫
      (perfectEndomorphismEnhancementAdjunction A D S E hgen).counit.app
        ((perfectEndomorphismTensorDG A D S E).onClosed.obj N) = 𝟙 _ :=
  (perfectEndomorphismEnhancementAdjunction A D S E hgen).left_triangle_components N

lemma perfectEndomorphismEnhancement_right_triangle
    (M : ClosedCategory A (PerfectDGModuleOver A D S)) :
    (perfectEndomorphismEnhancementAdjunction A D S E hgen).unit.app
        ((perfectEndomorphismDG A D S E hgen).onClosed.obj M) ≫
      (perfectEndomorphismDG A D S E hgen).onClosed.map
        ((perfectEndomorphismEnhancementAdjunction A D S E hgen).counit.app M) = 𝟙 _ :=
  (perfectEndomorphismEnhancementAdjunction A D S E hgen).right_triangle_components M

/-- enhancement制限の単位を包含で写すと、全加群の元の単位の可換図式になる。 -/
lemma perfectEndomorphismEnhancementUnit_inclusion
    (N : ClosedCategory A (PerfectDGModule A (EndomorphismObject E.val))) :
    (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onClosed.map
        ((perfectEndomorphismEnhancementAdjunction A D S E hgen).unit.app N) =
      (endomorphismModuleUnit A D E.val).app
          ((perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onClosed.obj N) ≫
        (endomorphismModuleHom A D E.val).onClosed.map
          ((perfectEndomorphismTensorClosedInclusionIso A D S E).hom.app N) ≫
        (perfectEndomorphismHomClosedInclusionIso A D S E hgen).hom.app
          ((perfectEndomorphismTensorDG A D S E).onClosed.obj N) := by
  unfold perfectEndomorphismEnhancementAdjunction
  exact Adjunction.map_restrictFullyFaithful_unit_app _ _ _ _ _ N

/-- enhancement制限の余単位を包含で写すと、全加群の元の合成評価の可換図式になる。 -/
lemma perfectEndomorphismEnhancementCounit_inclusion
    (M : ClosedCategory A (PerfectDGModuleOver A D S)) :
    (perfectDGModuleInclusion A D S).onClosed.map
        ((perfectEndomorphismEnhancementAdjunction A D S E hgen).counit.app M) =
      (perfectEndomorphismTensorClosedInclusionIso A D S E).inv.app
          ((perfectEndomorphismDG A D S E hgen).onClosed.obj M) ≫
        (endomorphismModuleTensor A D E.val).onClosed.map
          ((perfectEndomorphismHomClosedInclusionIso A D S E hgen).inv.app M) ≫
        (endomorphismModuleCounit A D E.val).app
          ((perfectDGModuleInclusion A D S).onClosed.obj M) := by
  unfold perfectEndomorphismEnhancementAdjunction
  exact Adjunction.map_restrictFullyFaithful_counit_app _ _ _ _ _ M

end SerrePositivity.DifferentialGraded
