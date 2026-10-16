module
public import SerrePositivity.DifferentialGraded.Derived.Coproducts
public import SerrePositivity.DifferentialGraded.Derived.Linear

/-! # 導来余積の成分射と有限supportへの射影 -/
@[expose] public section
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type u} (F : J → DerivedModuleCategory A D)

def moduleDerivedCoproductProjection (j : J) : (∐ F) ⟶ F j :=
  Sigma.desc (Pi.single j (𝟙 (F j)))

lemma moduleDerivedCoproductProjection_self (j : J) :
    Sigma.ι F j ≫ moduleDerivedCoproductProjection A D F j = 𝟙 (F j) := by
  simp [moduleDerivedCoproductProjection]

lemma moduleDerivedCoproductProjection_ne (i j : J) (h : i ≠ j) :
    Sigma.ι F i ≫ moduleDerivedCoproductProjection A D F j = 0 := by
  simp [moduleDerivedCoproductProjection, h]

def moduleDerivedCoproductFiniteProjection (t : Finset J) : (∐ F) ⟶ (∐ F) :=
  ∑ j ∈ t, moduleDerivedCoproductProjection A D F j ≫ Sigma.ι F j

lemma moduleDerivedCoproductFiniteProjection_mem (t : Finset J) (i : J) (hi : i ∈ t) :
    Sigma.ι F i ≫ moduleDerivedCoproductFiniteProjection A D F t = Sigma.ι F i := by
  rw [moduleDerivedCoproductFiniteProjection, comp_sum]
  calc
    _ = Sigma.ι F i ≫ moduleDerivedCoproductProjection A D F i ≫ Sigma.ι F i :=
      Finset.sum_eq_single i
        (fun j _ hji => by
          rw [← Category.assoc, moduleDerivedCoproductProjection_ne A D F i j (Ne.symm hji)]
          exact zero_comp)
        (fun h => (h hi).elim)
    _ = _ := by
      rw [← Category.assoc, moduleDerivedCoproductProjection_self, Category.id_comp]

lemma moduleDerivedCoproductComplement_mem (t : Finset J) (i : J) (hi : i ∈ t) :
    Sigma.ι F i ≫ (𝟙 (∐ F) - moduleDerivedCoproductFiniteProjection A D F t) = 0 := by
  rw [comp_sub, Category.comp_id, moduleDerivedCoproductFiniteProjection_mem A D F t i hi,
    sub_self]

end SerrePositivity.DifferentialGraded
