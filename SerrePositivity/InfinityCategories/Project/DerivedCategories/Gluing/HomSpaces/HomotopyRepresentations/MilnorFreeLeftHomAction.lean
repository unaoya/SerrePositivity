module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.MilnorFreeLeftNaturality
/-!
概要：元の左実延長の自由 Hom 作用は、固定した代表同型と Yoneda 評価で元代数射に戻る。
方針：全 Hom 自然性を代表同型の逆射で正規化する。
規約：同じ実延長と閉零同型の全次数共役を使う。
使われ方：元自由対角の Hom 比較の左射影。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source
local notation "C" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top
def dgGluingMilnorLeftRepresentableHomIso (x y : A) :
    moduleHom R (C) ((dgModuleExtension R (A) (C) (L)).obj (representable R x))
      ((dgModuleExtension R (A) (C) (L)).obj (representable R y)) ≅
    moduleHom R (C) (representable R ((L).obj x)) (representable R ((L).obj y)) :=
  enrichedClosedIsoHomIso (Complex R)
    (dgModuleExtensionRepresentableIso R (A) (C) (L) x)
    (dgModuleExtensionRepresentableIso R (A) (C) (L) y)
lemma dgGluingMilnorLeftRepresentable_conjugation (x y : A) :
    yonedaHom R (A) x y ≫ (dgModuleExtension R (A) (C) (L)).map
      (representable R x) (representable R y) ≫
      (dgGluingMilnorLeftRepresentableHomIso R d x y).hom =
    (L).map x y ≫ yonedaHom R (C) ((L).obj x) ((L).obj y) := by
  let P : moduleHom R (C) (representable R ((L).obj x)) (representable R ((L).obj y)) ≅
      moduleHom R (C) ((dgModuleExtension R (A) (C) (L)).obj (representable R x))
        (representable R ((L).obj y)) :=
    ((eHomFunctor (Complex R) («C» := ClosedCategory R (RightModule R (C)))).mapIso
      (dgModuleExtensionRepresentableIso R (A) (C) (L) x).op).app
        (ForgetEnrichment.of (Complex R) (representable R ((L).obj y)))
  have hc : (dgGluingMilnorLeftRepresentableHomIso R d x y).hom ≫ P.hom =
      moduleHomPostcompose R (C) _ _ _
        (dgModuleExtensionRepresentableIso R (A) (C) (L) y).hom :=
    enrichedClosedIsoConjugation_naturality (Complex R)
      (dgModuleExtensionRepresentableIso R (A) (C) (L) x)
      (dgModuleExtensionRepresentableIso R (A) (C) (L) y)
  apply (cancel_mono P.hom).mp
  calc
    _ = yonedaHom R (A) x y ≫ (dgModuleExtension R (A) (C) (L)).map
        (representable R x) (representable R y) ≫ moduleHomPostcompose R (C) _ _ _
          (dgModuleExtensionRepresentableIso R (A) (C) (L) y).hom := by
      simp only [Category.assoc, hc]
    _ = _ := by
      have hp : P.hom = moduleHomPrecompose R (C) _ _ _
          (dgModuleExtensionRepresentableIso R (A) (C) (L) x).hom := rfl
      rw [hp]
      simpa only [Category.assoc] using _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorLeftRepresentable_naturality R d x y
lemma dgGluingMilnorLeftRepresentable_evaluate (x y : A) :
    (dgModuleExtension R (A) (C) (L)).map (representable R x) (representable R y) ≫
      (dgGluingMilnorLeftRepresentableHomIso R d x y).hom ≫
      (dgYonedaIso R ((L).obj x) (representable R ((L).obj y))).hom =
    (dgYonedaIso R x (representable R y)).hom ≫ (L).map x y := by
  have : IsIso (yonedaHom R (A) x y) := by
    change IsIso (dgYonedaIso R x (representable R y)).inv
    infer_instance
  apply (cancel_epi (yonedaHom R (A) x y)).mp
  have h := congrArg (fun k => k ≫
    (dgYonedaIso R ((L).obj x) (representable R ((L).obj y))).hom)
    (dgGluingMilnorLeftRepresentable_conjugation R d x y)
  simp only [Category.assoc, yonedaHom, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] at h ⊢
  exact h
lemma dgGluingMilnorFreeLeftHomMap_evaluate :
    (dgSmallPerfectArrow R (A) (C) (L)).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSourceGenerator R d) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSourceGenerator R d) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftHomIso R d).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeSourceHomIso R d).hom ≫
      (L).map (dgOdotInputSourcePoint R d) (dgOdotInputSourcePoint R d) := by
  have h := dgGluingMilnorLeftRepresentable_evaluate R d
    (dgOdotInputSourcePoint R d) (dgOdotInputSourcePoint R d)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftHomIso, Iso.trans_hom,
    enrichedClosedIsoHomIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeSourceHomIso,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeLeftIso, dgGluingMilnorLeftRepresentableHomIso,
    enrichedClosedIsoConjugation] at h ⊢
  exact h
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
