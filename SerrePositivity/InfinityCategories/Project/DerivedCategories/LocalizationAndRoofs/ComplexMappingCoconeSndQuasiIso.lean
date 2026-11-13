module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexMappingCoconeMapIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.ComplexMappingCoconeBiprodQuasiIso
/-!
概要：第一成分の準同型性から、同じ mapping cocone の第二射影の準同型性を得る。
方針：二直和の実交換と cocone の実同型によって、既存の第一射影の判定へ戻す。
規約：実射影を変更しない。使われ方：普遍余単位の comma の標的への射影。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
/-- 第一成分が準同型なら、同じ二成分 cocone の実第二射影も準同型。 -/
lemma complexMappingCoconeProjectionSnd_quasiIso_of_eq {R : Type u} [CommRing R]
    {K L T : Complex R} (d : K ⊞ L ⟶ T) (a : K ⟶ T) (b : L ⟶ T)
    (hd : d = biprod.desc a b) (ha : QuasiIso a) :
    QuasiIso (mappingCocone.fst d ≫ (biprod.snd : K ⊞ L ⟶ L)) := by
  subst d
  let i : K ⊞ L ≅ L ⊞ K :=
    { hom := biprod.lift biprod.snd biprod.fst
      inv := biprod.lift biprod.snd biprod.fst
      hom_inv_id := by apply biprod.hom_ext <;> simp
      inv_hom_id := by apply biprod.hom_ext <;> simp }
  have h : biprod.desc a b ≫ (Iso.refl T).hom = i.hom ≫ biprod.desc b a := by
    apply biprod.hom_ext' <;> simp [i]
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso (biprod.desc a b) (biprod.desc b a) i (Iso.refl T) h
  have hw : e.hom ≫ (mappingCocone.fst (biprod.desc b a) ≫ biprod.fst) =
      mappingCocone.fst (biprod.desc a b) ≫ biprod.snd := by
    change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap (biprod.desc a b) (biprod.desc b a)
      i.hom (Iso.refl T).hom h ≫ _ = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst, Category.assoc]
    simp [i]
  have he : QuasiIso e.hom := quasiIso_of_isIso _
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodProjection_quasiIso b a ha
  have hc := quasiIso_comp e.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodProjection b a)
    (hφ := he) (hφ' := hp)
  change QuasiIso (e.hom ≫ (mappingCocone.fst (biprod.desc b a) ≫ biprod.fst)) at hc
  rw [hw] at hc
  exact hc
end SerrePositivity.InfinityCategories.Project.DerivedCategories
