module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.Codisk
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.IdentityCoconeHom

/-!
# 可縮 disk の全 Hom 同値

概要：P から次数 n−1,n の可縮 disk への射と Pⁿ→M を同一視する。
方針：恒等 mapping cocone の実 cochain 表示と single への cochain 同値を合成。
規約：全 Hom と元の始域射との自然性を保持する。
使われ方：各次数の評価関手の実右随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.CochainComplex _root_.CochainComplex.HomComplex
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

def codiskHomEquiv (P : Complex A) (M : ModuleCat.{u} A) (n : ℤ) :
    (P ⟶ _root_.SerrePositivity.ComplexLimits.codisk M n) ≃ (P.X n ⟶ M) :=
  (_root_.SerrePositivity.ComplexLimits.identityCoconeHomEquiv P ((single (ModuleCat A) (.up ℤ) (n - 1)).obj M)).trans
    (Cochain.toSingleEquiv (show n + (-1) = n - 1 by omega)).toEquiv

lemma codiskHomEquiv_apply (P : Complex A) (M : ModuleCat.{u} A) (n : ℤ)
    (f : P ⟶ _root_.SerrePositivity.ComplexLimits.codisk M n) : _root_.SerrePositivity.ComplexLimits.codiskHomEquiv P M n f =
      f.f n ≫ (mappingCocone.snd (𝟙 ((single (ModuleCat A) (.up ℤ) (n - 1)).obj M))).v
        n (n - 1) (by omega) ≫ (singleObjXSelf (.up ℤ) (n - 1) M).hom := by
  change ((Cochain.ofHom f).comp _ (zero_add (-1))).v n (n - 1) (by omega) ≫ _ = _
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Category.assoc]

lemma codiskHomEquiv_precomp {P P' : Complex A} (M : ModuleCat.{u} A) (n : ℤ)
    (f : P' ⟶ P) (g : P ⟶ _root_.SerrePositivity.ComplexLimits.codisk M n) :
    _root_.SerrePositivity.ComplexLimits.codiskHomEquiv P' M n (f ≫ g) = f.f n ≫ _root_.SerrePositivity.ComplexLimits.codiskHomEquiv P M n g := by
  simp only [_root_.SerrePositivity.ComplexLimits.codiskHomEquiv_apply, HomologicalComplex.comp_f, Category.assoc]

lemma codiskHomEquiv_symm_precomp {P P' : Complex A} (M : ModuleCat.{u} A) (n : ℤ)
    (f : P' ⟶ P) (g : P.X n ⟶ M) :
    (_root_.SerrePositivity.ComplexLimits.codiskHomEquiv P' M n).symm (f.f n ≫ g) = f ≫ (_root_.SerrePositivity.ComplexLimits.codiskHomEquiv P M n).symm g := by
  apply (_root_.SerrePositivity.ComplexLimits.codiskHomEquiv P' M n).injective
  rw [Equiv.apply_symm_apply, _root_.SerrePositivity.ComplexLimits.codiskHomEquiv_precomp, Equiv.apply_symm_apply]

end SerrePositivity.ComplexLimits
