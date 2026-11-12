module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.YonedaHomCone

/-! 元の Yoneda 円錐同型を、両端の Yoneda 写像と標準 Hom 円錐比較で回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex
open DifferentialGraded
variable (R : Type u) [CommRing R]

/-- 等しい射の間の恒等正方形は、同じ等式による円錐の移送そのもの。 -/
lemma dgGluingConeMap_eqToIso {A B : Complex R} (f g : A ⟶ B) (h : f = g)
    (comm : f ≫ 𝟙 B = 𝟙 A ≫ g) :
    mappingCone.map f g (𝟙 A) (𝟙 B) comm =
      (eqToIso (congrArg (fun a : A ⟶ B => mappingCone a) h)).hom := by
  subst g
  simpa only [eqToIso_refl, Iso.refl_hom] using mappingCone.map_id f

variable (C : Type v) [DGCategory R C] [Small.{u} C] (x y z : C)
  (f : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z)
local notation "r" => eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) x) f
local notation "T" => ForgetEnrichment.of (Complex R) (representable R x)
local notation "yf" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (dgYoneda R C)) f
local notation "K" => ForgetEnrichment.to (Complex R) (moduleCone R C yf)

/-- 元の閉射の Hom 後合成と Yoneda 像の全 Hom 後合成の厳密正方形。 -/
lemma dgGluingYonedaCone_square :
    r ≫ yonedaHom R C x z =
      yonedaHom R C x y ≫ eHomWhiskerLeft (Complex R) T yf :=
  dgHomMap_postcompose (dgYoneda R C) (ForgetEnrichment.of (Complex R) x) f

/-- 元の Hom 円錐から、同じ Yoneda 像の Hom 後合成円錐への標準写像。 -/
def dgGluingYonedaConeMap : mappingCone r ≅
    mappingCone (eHomWhiskerLeft (Complex R) T yf) where
  hom := mappingCone.map r (eHomWhiskerLeft (Complex R) T yf)
    (yonedaHom R C x y) (yonedaHom R C x z) (dgGluingYonedaCone_square R C x y z f)
  inv := mappingCone.map (eHomWhiskerLeft (Complex R) T yf) r
    (dgYonedaIso R x (representable R y)).hom (dgYonedaIso R x (representable R z)).hom
    (by
      have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_postcompose R C x ((dgYoneda R C).onClosed.map f)
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_evaluate] at hn
      exact hn)
  hom_inv_id := by
    rw [← mappingCone.map_comp]
    simpa only [yonedaHom, Iso.inv_hom_id] using mappingCone.map_id r
  inv_hom_id := by
    rw [← mappingCone.map_comp]
    simpa only [yonedaHom, Iso.hom_inv_id] using
      mappingCone.map_id (eHomWhiskerLeft (Complex R) T yf)

/-- 既存の Yoneda 円錐同型は、両端の Yoneda と同じ標準 Hom 円錐比較から得られる。 -/
lemma dgGluingYonedaConeIso_canonical :
    (dgGluingYonedaConeMap R C x y z f).hom ≫ moduleHomConeComparison R C T yf =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeIso R C x y z f).hom := by
  apply (cancel_mono (dgYonedaIso R x K).hom).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaHomConeComparison]
  dsimp only [dgGluingYonedaConeMap]
  rw [← mappingCone.map_comp]
  change mappingCone.map r ((moduleEvaluation R C x).map yf)
    ((dgYonedaIso R x (representable R y)).inv ≫ (dgYonedaIso R x (representable R y)).hom)
    ((dgYonedaIso R x (representable R z)).inv ≫ (dgYonedaIso R x (representable R z)).hom)
    (by simpa only [Iso.inv_hom_id, Category.comp_id, Category.id_comp] using
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_evaluate R C x y z f).symm) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeIso R C x y z f).hom ≫ (dgYonedaIso R x K).hom
  simp only [Iso.inv_hom_id]
  rw [dgGluingConeMap_eqToIso R r ((moduleEvaluation R C x).map yf)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_evaluate R C x y z f).symm]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- 元の円錐同型の右包含は Yoneda と元の加群円錐の閉包含で与えられる。 -/
lemma dgGluingYonedaConeIso_inr :
    mappingCone.inr r ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeIso R C x y z f).hom =
    yonedaHom R C x z ≫ eHomWhiskerLeft (Complex R) T (moduleConeInr R C yf) := by
  rw [← dgGluingYonedaConeIso_canonical]
  apply HomologicalComplex.hom_ext
  intro n
  simp only [dgGluingYonedaConeMap, HomologicalComplex.comp_f, mappingCone.map,
    mappingCone.inr_f_desc_f_assoc, moduleHomConeComparison, mappingCone.inr_f_desc_f,
    HomologicalComplex.comp_f, Category.assoc]

/-- 元の円錐同型の左包含は、同じ全 Hom 円錐比較の次数 −1 包含で与えられる。 -/
lemma dgGluingYonedaConeIso_inl :
    (mappingCone.inl r).comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeIso R C x y z f).hom)
      (add_zero (-1)) =
    (Cochain.ofHom (yonedaHom R C x y)).comp (moduleHomConeLeftCochain R C T yf)
      (zero_add (-1)) := by
  rw [← dgGluingYonedaConeIso_canonical]
  apply Cochain.ext
  intro q n hn
  simp only [dgGluingYonedaConeMap, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    HomologicalComplex.comp_f, mappingCone.map, mappingCone.inl_v_desc_f_assoc,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v, moduleHomConeComparison,
    mappingCone.inl_v_desc_f, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
