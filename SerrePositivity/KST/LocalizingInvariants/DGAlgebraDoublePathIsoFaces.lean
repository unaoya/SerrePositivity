module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathFunctor

/-!
概要：指定した代数同型で二重経路を戻し、元の四辺を回収する。
方針：経路関手の合成則と評価の自然性により、同型と逆同型を消去する。
規約：四辺は全経路として比較する。使われ方：native 係数への W 正方形の移送。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] {C D T : Mon (Complex R)} (e : C ≅ D)
  (z : T ⟶ algebra R (algebra R D)) (u : T ⟶ algebra R C)

def pullbackDoubleIso : T ⟶ algebra R (algebra R C) :=
  z ≫ map R (map R e.inv)

lemma pullbackDoubleIso_source
    (h : z ≫ source R (algebra R D) = u ≫ map R e.hom) :
    pullbackDoubleIso R e z ≫ source R (algebra R C) = u := by
  rw [pullbackDoubleIso, Category.assoc, map_source, ← Category.assoc, h,
    Category.assoc, ← map_comp, e.hom_inv_id, map_id, Category.comp_id]

lemma pullbackDoubleIso_target
    (h : z ≫ target R (algebra R D) = u ≫ map R e.hom) :
    pullbackDoubleIso R e z ≫ target R (algebra R C) = u := by
  rw [pullbackDoubleIso, Category.assoc, map_target, ← Category.assoc, h,
    Category.assoc, ← map_comp, e.hom_inv_id, map_id, Category.comp_id]

lemma pullbackDoubleIso_innerSource
    (h : z ≫ map R (source R D) = u ≫ map R e.hom) :
    pullbackDoubleIso R e z ≫ map R (source R C) = u := by
  rw [pullbackDoubleIso, Category.assoc, ← map_comp, map_source, map_comp,
    ← Category.assoc, h, Category.assoc, ← map_comp, e.hom_inv_id, map_id,
    Category.comp_id]

lemma pullbackDoubleIso_innerTarget
    (h : z ≫ map R (target R D) = u ≫ map R e.hom) :
    pullbackDoubleIso R e z ≫ map R (target R C) = u := by
  rw [pullbackDoubleIso, Category.assoc, ← map_comp, map_target, map_comp,
    ← Category.assoc, h, Category.assoc, ← map_comp, e.hom_inv_id, map_id,
    Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
