module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathProjection

/-!
概要：実乗法的経路を、mapping-path への元の射と厳密な比較四角形へ移す。
方針：源の恒等射と指定経路を普遍 lift へ渡し、射影への合成が恒等なので準同型性を得る。
規約：経路の反転は使用しない。使われ方：classifying cospan の準同型 zigzag。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathCospanComparison
variable (R : Type u) [CommRing R] {A B W : Mon (Complex R)} (f : A ⟶ B)
  (a : W ⟶ B) (q : W ⟶ A) (h : Path.Witness R a (q ≫ f))

def witnessMap : W ⟶ MappingPath.algebra R a :=
  MappingPath.lift R a h.hom (𝟙 W) (by rw [h.source_eq, Category.id_comp])

lemma witnessMap_projection : witnessMap R f a q h ≫ MappingPath.projection R a = 𝟙 W :=
  MappingPath.lift_projection R _ _ _ _

lemma witnessMap_target : witnessMap R f a q h ≫ MappingPath.target R a = q ≫ f :=
  (MappingPath.lift_target R _ _ _ _).trans h.target_eq

lemma witnessMap_quasiIso : QuasiIso (witnessMap R f a q h).hom := by
  have := MappingPath.projection_quasiIso R a
  have : QuasiIso ((witnessMap R f a q h).hom ≫ (MappingPath.projection R a).hom) := by
    change QuasiIso (witnessMap R f a q h ≫ MappingPath.projection R a).hom
    rw [witnessMap_projection]
    infer_instance
  exact quasiIso_of_comp_right (witnessMap R f a q h).hom (MappingPath.projection R a).hom

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathCospanComparison
