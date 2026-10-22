module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSurjectiveRoofConnectiveValue

/-!
概要：準同型の逆の実 roof を、connective 準同型だけを反転する関手で評価する。
方針：分母の源の connective 性を元の準同型から導き、元の経路と切断で両三角形を保つ。
規約：元の準同型の終域の connective 性だけを使う。使われ方：元の実不変量値。
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
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)
  (hL : InvertsConnectiveQuasiIsos R L) (hB : IsConnective R B) (hf : QuasiIso f.hom)

lemma inverse_connectiveValue_comp :
    connectiveValue R L hL hB (ofQuasiIsoInverse R f hf) ≫ L.map f = 𝟙 _ := by
  have := hL (apex_isConnective R (ofQuasiIsoInverse R f hf) hB) hB
    (MappingPath.target R f) (MappingPath.target_quasiIso R f hf)
  have he := (MappingPath.pathWitness R f).map_eq_of_connective R L hL hB
  change (inv (L.map (MappingPath.target R f)) ≫ L.map (MappingPath.projection R f)) ≫
    L.map f = 𝟙 _
  rw [Category.assoc, ← L.map_comp, he, IsIso.inv_hom_id]

lemma comp_inverse_connectiveValue :
    L.map f ≫ connectiveValue R L hL hB (ofQuasiIsoInverse R f hf) = 𝟙 _ := by
  have := hL (apex_isConnective R (ofQuasiIsoInverse R f hf) hB) hB
    (MappingPath.target R f) (MappingPath.target_quasiIso R f hf)
  have he : L.map f = L.map (MappingPath.section_ R f) ≫ L.map (MappingPath.target R f) := by
    rw [← L.map_comp]
    exact congrArg L.map (MappingPath.section_target R f).symm
  change L.map f ≫ (inv (L.map (MappingPath.target R f)) ≫
    L.map (MappingPath.projection R f)) = 𝟙 _
  rw [he, Category.assoc, IsIso.hom_inv_id_assoc, ← L.map_comp,
    MappingPath.section_projection, L.map_id]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof
