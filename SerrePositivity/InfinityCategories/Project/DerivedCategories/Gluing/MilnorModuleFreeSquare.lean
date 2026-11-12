module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.MilnorFreeHomComponents
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.ExtensionRepresentableComposition
/-!
概要：Milnor 四角形の実二回延長と自由代表比較の整合を、元の比較射について証明する。
方針：D-19 の代表上の合成則を両脚へ適用し、入力等号の輸送を保持する。
規約：同じ実合成比較・代表同型を使い、自由対象を選び直さない。
使われ方：元自由対角の比較差を Milnor fiber の差へ送る正方形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source
local notation "C" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left
local notation "D" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper
local notation "a" => dgOdotInputSourcePoint R d
lemma dgGluingMilnorModuleFreeSquare :
    ((dgModuleExtensionCompositionAt R (A) (C) (E) (L) (p) (representable R (a))).hom ≫
      (dgModuleExtensionInputIso R (A) (E) (dgOdotInput_dg_commutes R d)
        (representable R (a))).hom ≫
      (dgModuleExtensionCompositionAt R (A) (D) (E) (G) (q) (representable R (a))).inv) ≫
      ((dgModuleExtension R (D) (E) (q)).onClosed.map
          (dgModuleExtensionRepresentableIso R (A) (D) (G) (a)).hom ≫
        (dgModuleExtensionRepresentableIso R (D) (E) (q) ((G).obj (a))).hom) =
    (dgModuleExtension R (C) (E) (p)).onClosed.map
        (dgModuleExtensionRepresentableIso R (A) (C) (L) (a)).hom ≫
      (dgModuleExtensionRepresentableIso R (C) (E) (p) ((L).obj (a))).hom := by
  have hi0 {F H : DGFunctor R (A) (E)} (h : F = H) :
      (dgModuleExtensionInputIso R (A) (E) h (representable R (a))).hom ≫
        (dgModuleExtensionRepresentableIso R (A) (E) H (a)).hom =
      (dgModuleExtensionRepresentableIso R (A) (E) F (a)).hom ≫
        eqToHom (congrArg (fun J : DGFunctor R (A) (E) =>
          ForgetEnrichment.of (Complex R) (representable R (J.obj (a)))) h) := by
    cases h
    simp only [dgModuleExtensionInputIso, eqToIso_refl, Iso.refl_hom,
      eqToHom_refl, Category.id_comp, Category.comp_id]
  have hi := hi0 (dgOdotInput_dg_commutes R d)
  simp only [eqToHom_refl, Category.comp_id] at hi
  have hl := dgModuleExtensionCompositionAt_representable R (A) (C) (E) (L) (p) (a)
  have hr := dgModuleExtensionCompositionAt_representable R (A) (D) (E) (G) (q) (a)
  rw [← hr]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hi]
  exact hl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
