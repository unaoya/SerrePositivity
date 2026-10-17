module
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectTensor
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # 再構成導来随伴の主Perf制限と実際のtensor逆関手 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)

/-- 全導来圏での実際のtensor–Hom随伴を、完全忠実な包含に沿って制限する。 -/
def perfectEndomorphismAdjunction :
    perfectEndomorphismTensorToPerfect A D S E ⊣
      perfectEndomorphismHomToPerfect A D S E hgen :=
  (endomorphismDerivedAdjunction A D E.val E.property.1).restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful (modulePerfect A (EndomorphismObject E.val)).ι)
    (Functor.FullyFaithful.ofFullyFaithful (modulePerfectOver A D S).ι)
    (perfectEndomorphismTensorInclusionIso A D S E).symm
    (perfectEndomorphismHomInclusionIso A D S E hgen).symm

lemma perfectEndomorphismUnit_inclusion
    (N : PerfectModuleCategory A (EndomorphismObject E.val)) :
    (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).map
        ((perfectEndomorphismAdjunction A D S E hgen).unit.app N) =
      (endomorphismDerivedUnit A D E.val E.property.1).app N.obj := by
  unfold perfectEndomorphismAdjunction
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  change (endomorphismDerivedAdjunction A D E.val E.property.1).unit.app N.obj ≫
    (endomorphismDerivedHom A D E.val E.property.1).map (𝟙 _) ≫ 𝟙 _ = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact Category.comp_id _

lemma perfectEndomorphismCounit_inclusion (M : PerfectModuleCategoryOver A D S) :
    (perfectModuleInclusion A D S).map
        ((perfectEndomorphismAdjunction A D S E hgen).counit.app M) =
      (endomorphismDerivedCounit A D E.val E.property.1).app M.obj := by
  unfold perfectEndomorphismAdjunction
  rw [Adjunction.map_restrictFullyFaithful_counit_app]
  change 𝟙 _ ≫ (endomorphismDerivedTensor A D E.val).map (𝟙 _) ≫
    (endomorphismDerivedAdjunction A D E.val E.property.1).counit.app M.obj = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

lemma perfectEndomorphismUnit_isIso :
    IsIso (perfectEndomorphismAdjunction A D S E hgen).unit := by infer_instance

lemma perfectEndomorphismCounit_isIso :
    IsIso (perfectEndomorphismAdjunction A D S E hgen).counit := by infer_instance

include hgen in
lemma perfectEndomorphismTensor_isEquivalence :
    (perfectEndomorphismTensorToPerfect A D S E).IsEquivalence :=
  (perfectEndomorphismAdjunction A D S E hgen).isEquivalence_left_of_isEquivalence_right

/-- 既存の主Perf同値の逆は、実際の再構成導来tensorの制限と自然同型である。 -/
def perfectEndomorphismTensorInverseIso :
    perfectEndomorphismTensorToPerfect A D S E ≅
      (perfectEndomorphismEquivalence A D S E hgen).inverse :=
  (perfectEndomorphismAdjunction A D S E hgen).leftAdjointUniq
    (perfectEndomorphismEquivalence A D S E hgen).symm.toAdjunction

end SerrePositivity.DifferentialGraded
