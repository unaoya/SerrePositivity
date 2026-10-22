module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSurjectiveRoofValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathProjection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathSurjective

/-!
概要：元の準同型の逆を、次数全射準同型を分母とする実 dg 代数 roof で表す。
方針：元の MappingPath target と projection を使い、元の経路と切断で逆三角形を示す。
規約：局所化の一般分数表示は使わない。使われ方：一切断の実逆の抽出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} (f : A ⟶ B)

def ofQuasiIsoInverse (hf : QuasiIso f.hom) : SurjectiveRoof R B A where
  apex := MappingPath.algebra R f
  denominator := MappingPath.target R f
  numerator := MappingPath.projection R f
  denominator_epi := MappingPath.target_epi R f
  denominator_quasiIso := MappingPath.target_quasiIso R f hf

variable {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)
  (hL : InvertsQuasiIsos R L) (hf : QuasiIso f.hom)

lemma inverse_value_comp : value R L hL (ofQuasiIsoInverse R f hf) ≫ L.map f = 𝟙 _ := by
  have := hL (MappingPath.target R f) (MappingPath.target_quasiIso R f hf)
  have he := (MappingPath.pathWitness R f).map_eq R L hL
  change (inv (L.map (MappingPath.target R f)) ≫ L.map (MappingPath.projection R f)) ≫
    L.map f = 𝟙 _
  rw [Category.assoc, ← L.map_comp, he, IsIso.inv_hom_id]

lemma comp_inverse_value : L.map f ≫ value R L hL (ofQuasiIsoInverse R f hf) = 𝟙 _ := by
  have := hL (MappingPath.target R f) (MappingPath.target_quasiIso R f hf)
  have he : L.map f = L.map (MappingPath.section_ R f) ≫ L.map (MappingPath.target R f) := by
    rw [← L.map_comp]
    exact congrArg L.map (MappingPath.section_target R f).symm
  change L.map f ≫ (inv (L.map (MappingPath.target R f)) ≫
    L.map (MappingPath.projection R f)) = 𝟙 _
  rw [he, Category.assoc, IsIso.hom_inv_id_assoc, ← L.map_comp,
    MappingPath.section_projection, L.map_id]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof
