module

public import SerrePositivity.KST.LocalizingInvariants.CochainPullbackCoconeComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackCoconeIso

/-!
概要：一脚が次数全射な実代数 cospan の通常 pullback と経路模型を準同型で比較。
方針：元の比較射の二射影と零 cochain を保ち、kernel–cocone の比較へ同定する。
規約：一般の ∞ 極限普遍性は主張しない。使われ方：Postnikov の非分裂拡大の模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)} (f : A ⟶ B) (g : C ⟶ B)

lemma comparison_primitive :
    (Cochain.ofHom (comparison R f g).hom).comp (primitive R f g) (zero_add (-1)) = 0 := by
  have hp : (comparison R f g).hom ≫ (path R f g).hom =
      (MonoidPullback.fst f g).hom ≫ f.hom ≫ (Path.diagonal R B).hom :=
    congrArg Mon.Hom.hom (comparison_path R f g)
  have hd : (Cochain.ofHom (Path.diagonal R B).hom).comp
      (Path.primitive R B) (zero_add (-1)) = 0 := Path.diagonalHom_primitive R B
  change (Cochain.ofHom (comparison R f g).hom).comp
    ((Cochain.ofHom (path R f g).hom).comp (Path.primitive R B) _) _ = 0
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, hp]
  have ht : (MonoidPullback.fst f g).hom ≫ f.hom ≫ (Path.diagonal R B).hom =
      ((MonoidPullback.fst f g).hom ≫ f.hom) ≫ (Path.diagonal R B).hom :=
    (Category.assoc _ _ _).symm
  rw [ht, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    hd, Cochain.comp_zero]

lemma comparison_toMappingCocone :
    (comparison R f g).hom ≫ toMappingCocone R f g =
      cochainPullbackToCocone f.hom g.hom := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappingCocone_hom_ext (difference R f g)
  · calc
      _ = (comparison R f g).hom ≫ pairHom R f g := by
        rw [Category.assoc, toMappingCocone_fst]
      _ = biprod.lift (MonoidPullback.fst f g).hom (MonoidPullback.snd f g).hom := by
        apply biprod.hom_ext
        · rw [Category.assoc, pairHom_fst, biprod.lift_fst]
          exact congrArg Mon.Hom.hom (comparison_left R f g)
        · rw [Category.assoc, pairHom_snd, biprod.lift_snd]
          exact congrArg Mon.Hom.hom (comparison_right R f g)
      _ = _ := (cochainPullbackToCocone_fst f.hom g.hom).symm
  · calc
      _ = (Cochain.ofHom (comparison R f g).hom).comp (primitive R f g) _ := by
        rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
          toMappingCocone_snd]
      _ = 0 := comparison_primitive R f g
      _ = _ := (cochainPullbackToCocone_snd f.hom g.hom).symm

lemma comparison_quasiIso_of_difference_epi [Epi (difference R f g)] :
    QuasiIso (comparison R f g).hom := by
  have : QuasiIso ((comparison R f g).hom ≫ toMappingCocone R f g) := by
    rw [comparison_toMappingCocone]
    have : Epi (cochainPullbackDifference f.hom g.hom) := ‹Epi (difference R f g)›
    exact cochainPullbackToCocone_quasiIso f.hom g.hom
  have : QuasiIso (toMappingCocone R f g) := quasiIso_of_isIso (complexIso R f g).hom
  exact quasiIso_of_comp_right (comparison R f g).hom (toMappingCocone R f g)

lemma comparison_quasiIso_left [Epi f.hom] : QuasiIso (comparison R f g).hom := by
  have : Epi (difference R f g) := cochainPullbackDifference_epi_left f.hom g.hom
  exact comparison_quasiIso_of_difference_epi R f g

lemma comparison_quasiIso_right [Epi g.hom] : QuasiIso (comparison R f g).hom := by
  have : Epi (difference R f g) := cochainPullbackDifference_epi_right f.hom g.hom
  exact comparison_quasiIso_of_difference_epi R f g

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
