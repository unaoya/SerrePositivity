module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxInputCoordinates
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedPairProjections
/-!
概要：元 lax 比較の入力座標を元左右 Hom 鎖射影へ厳密に回収する。
方針：実 nerve の作用を Hom 鎖写像へ移し、同じ Hom 模型同型の往復を相殺する。
規約：左右順序と全次数を保持する。使われ方：元二脚の全比較の座標照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetLaxHomLeftRawInput_action :
    (dgGluingHomMappingIso R C D M X Y).inv ≫
      pinchedHomMap (dgNerve.map (dgGluingLeft R C D M))
        (Simplex.vertex X) (Simplex.vertex Y) ≫
        (dgGluingHomTargetLaxHomLeftRawInputIso R C D E p q X Y).hom =
    complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y) := by
  simp only [dgGluingHomTargetLaxHomLeftRawInputIso, Iso.trans_hom, Category.assoc]
  rw [reassoc_of% dgFunctor_pinchedHomMap_eq]
  erw [pinchedComplexModelIso_naturality ((dgGluingLeft R C D M).map X Y)]
  simp only [dgGluingHomMappingIso, Iso.inv_hom_id_assoc]
  rfl

lemma dgGluingHomTargetLaxHomRightRawInput_action :
    (dgGluingHomMappingIso R C D M X Y).inv ≫
      pinchedHomMap (dgNerve.map (dgGluingRight R C D M))
        (Simplex.vertex X) (Simplex.vertex Y) ≫
        (dgGluingHomTargetLaxHomRightRawInputIso R C D E p q X Y).hom =
    complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y) := by
  simp only [dgGluingHomTargetLaxHomRightRawInputIso, Iso.trans_hom, Category.assoc]
  rw [reassoc_of% dgFunctor_pinchedHomMap_eq]
  erw [pinchedComplexModelIso_naturality ((dgGluingRight R C D M).map X Y)]
  simp only [dgGluingHomMappingIso, Iso.inv_hom_id_assoc]
  rw [dgGluingRight_map]

lemma dgGluingHomTargetLaxHomPullbackComparison_raw_inputs :
    dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y ≫
      dgGluingHomTargetLaxHomInputProjection R C D E p q X Y ≫
        (dgGluingHomTargetLaxHomRawInputIso R C D E p q X Y).hom =
    lift (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y))
      (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y)) := by
  simp only [dgGluingHomTargetLaxHomRawInputIso, Iso.trans_hom, Category.assoc]
  rw [reassoc_of% dgGluingHomTargetLaxHomPullbackComparison_inputs_transport R C D E p q X Y]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [tensorIso_hom, Category.assoc, tensorHom_fst, lift_fst]
    rw [reassoc_of% dgGluingPinchedPairMap_first]
    exact dgGluingHomTargetLaxHomLeftRawInput_action R C D E p q X Y
  · simp only [tensorIso_hom, Category.assoc, tensorHom_snd, lift_snd]
    rw [reassoc_of% dgGluingPinchedPairMap_second]
    exact dgGluingHomTargetLaxHomRightRawInput_action R C D E p q X Y

end SerrePositivity.InfinityCategories
