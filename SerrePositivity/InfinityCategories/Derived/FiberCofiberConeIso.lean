module
public import SerrePositivity.InfinityCategories.Derived.FiberCofiberDesc

/-! # 二射影の cofiber と cocone 射影の cone の符号比較

概要：直和の第二成分の符号を直して、二射影の差を mapping cocone の第一射影へ同定する。
方針：biproduct の符号同型を cone の可換四角形へ渡す。
規約：元の二射の和も同じ符号同型で差に変換する。使われ方：D7 の双対比較の同値性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve CochainComplex HomComplex
variable {S : Type u} [CommRing S] {B C D : Complex S}

/-- 二射影の差は cocone の第一射影の後の符号反転。 -/
lemma fiberCofiberDifference_eq (g : B ⟶ D) (h : C ⟶ D) :
    cofiberDifference (pullbackProjectionB g h) (pullbackProjectionC g h) =
      mappingCocone.fst (fiberDifference g h) ≫ (cofiberBiproductSignIso B C).hom := by
  rw [← fiberProjection_eq_mappingCocone_fst]
  apply biprod.hom_ext <;>
    simp [cofiberDifference, pullbackProjectionB, pullbackProjectionC,
      cofiberBiproductSignIso, Category.assoc]

/-- 直和の符号反転は二射の差を二射の和へ変える。 -/
lemma fiberSignDifference_sum (g : B ⟶ D) (h : C ⟶ D) :
    (cofiberBiproductSignIso B C).inv ≫ fiberDifference g h = fiberSumMap g h := by
  apply biprod.hom_ext' <;>
    simp [cofiberBiproductSignIso, fiberDifference, fiberSumMap, ← Category.assoc]

/-- 二射影の差の cone と cocone 第一射影の cone の同型。 -/
def fiberInputConeIso (g : B ⟶ D) (h : C ⟶ D) :
    pushoutCofiber (pullbackProjectionB g h) (pullbackProjectionC g h) ≅
      mappingCone (mappingCocone.fst (fiberDifference g h)) where
  hom := mappingCone.map _ _ (𝟙 _) (cofiberBiproductSignIso B C).inv (by
    rw [Category.id_comp, fiberCofiberDifference_eq, Category.assoc, Iso.hom_inv_id,
      Category.comp_id])
  inv := mappingCone.map _ _ (𝟙 _) (cofiberBiproductSignIso B C).hom (by
    rw [Category.id_comp, fiberCofiberDifference_eq])
  hom_inv_id := by
    rw [← mappingCone.map_comp]
    simp only [Category.id_comp, Iso.inv_hom_id]
    exact mappingCone.map_id _
  inv_hom_id := by
    rw [← mappingCone.map_comp]
    simp only [Category.id_comp, Iso.hom_inv_id]
    exact mappingCone.map_id _

end SerrePositivity.InfinityCategories
