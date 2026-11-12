module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackSourceMap
public import SerrePositivity.KST.LocalizingInvariants.CochainBiprodQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.CochainMappingCoconeMapQuasiIso

/-!
概要：cospan の一脚の始域の準同型置換は、元の homotopy pullback 模型でも準同型を誘導。
方針：実二脚・比較 cochain を保つ射を、差の cocone の準同型射へ同定する。
規約：実代数射を構成してから準同型性を示す。使われ方：cell 上の Postnikov 拡大。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A A' B C : Mon (Complex R)}
  (f : A ⟶ B) (g : C ⟶ B) (a : A' ⟶ A)

lemma sourceMap_toMappingCocone : (sourceMap R f g a).hom ≫ toMappingCocone R f g =
    toMappingCocone R (a ≫ f) g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap (difference R (a ≫ f) g)
      (difference R f g) (sourceSumMap R a) (𝟙 B.X) (sourceDifference_comm R f g a) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappingCocone_hom_ext (difference R f g)
  · rw [Category.assoc, toMappingCocone_fst, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst, ← Category.assoc, toMappingCocone_fst]
    apply biprod.hom_ext
    · rw [Category.assoc, pairHom_fst, Category.assoc, sourceSumMap, biprod.map_fst,
        ← Category.assoc, pairHom_fst]
      exact congrArg Mon.Hom.hom (sourceMap_left R f g a)
    · rw [Category.assoc, pairHom_snd, Category.assoc, sourceSumMap, biprod.map_snd,
        Category.comp_id, pairHom_snd]
      exact congrArg Mon.Hom.hom (sourceMap_right R f g a)
  · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      toMappingCocone_snd, sourceMap_primitive]
    rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd, Cochain.comp_id, toMappingCocone_snd]

lemma sourceMap_quasiIso (ha : QuasiIso a.hom) : QuasiIso (sourceMap R f g a).hom := by
  have hs : QuasiIso (sourceSumMap R a (C := C)) :=
    cochainBiprodMap_quasiIso a.hom (𝟙 C.X) ha (quasiIso_of_isIso _)
  have hc : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap (difference R (a ≫ f) g)
      (difference R f g) (sourceSumMap R a) (𝟙 B.X) (sourceDifference_comm R f g a)) :=
    cochainMappingCoconeMap_quasiIso _ _ _ _ _ hs (quasiIso_of_isIso _)
  have ht : QuasiIso ((sourceMap R f g a).hom ≫ toMappingCocone R f g) := by
    rw [sourceMap_toMappingCocone]
    exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso (complexIso R (a ≫ f) g).hom) (hφ' := hc)
  have : QuasiIso (toMappingCocone R f g) := quasiIso_of_isIso (complexIso R f g).hom
  exact quasiIso_of_comp_right (sourceMap R f g a).hom (toMappingCocone R f g)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
