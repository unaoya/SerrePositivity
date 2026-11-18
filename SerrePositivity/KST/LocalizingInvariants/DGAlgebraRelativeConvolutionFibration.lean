module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeConvolutionUnderlying
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSimplicialConvolutionRestriction
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ProjectivePullbackHom

/-!
概要：実相対 AW 制限は、正規化 cofibration と全射標的射に対して全射。
方針：同じ元の複体の pullback-Hom と両射影で比較し、E2 の証拠を移す。
規約：正規化像が擬同型なら同じ実制限射も擬同型。モデル構造の入力は不要。
使われ方：cell 源の固定底ホーン充填と写像の Kan fibration 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {X B : Mon (Complex R)}
  (q : X ⟶ B) {K L : SSet.{0}} (f : K ⟶ L)

lemma relativeConvolutionRestriction_underlying_compare :
    (relativeConvolutionRestriction R q f).hom ≫
      (relativeConvolutionRestrictionUnderlyingIso R q f).hom =
        _root_.SerrePositivity.ComplexLimits.complexPullbackHom
          ((EInfinity.BarrattEccles.normalizedFunctor R).map f) q.hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, relativeConvolutionRestrictionUnderlyingIso_fst,
      _root_.SerrePositivity.ComplexLimits.complexPullbackHom_fst]
    change (relativeConvolutionRestriction R q f ≫
      relativeConvolutionRestrictionFst R q f).hom = _
    rw [relativeConvolutionRestriction_fst, simplicialConvolutionRestriction_hom]
  · rw [Category.assoc, relativeConvolutionRestrictionUnderlyingIso_snd,
      _root_.SerrePositivity.ComplexLimits.complexPullbackHom_snd]
    change (relativeConvolutionRestriction R q f ≫
      relativeConvolutionRestrictionSnd R q f).hom = _
    rw [relativeConvolutionRestriction_snd, simplicialConvolutionTargetNatTrans_hom]

lemma relativeConvolutionRestriction_hom_eq :
    (relativeConvolutionRestriction R q f).hom =
      _root_.SerrePositivity.ComplexLimits.complexPullbackHom
        ((EInfinity.BarrattEccles.normalizedFunctor R).map f) q.hom ≫
          (relativeConvolutionRestrictionUnderlyingIso R q f).inv :=
  (Iso.eq_comp_inv _).mpr (relativeConvolutionRestriction_underlying_compare R q f)

variable [Mono f]

lemma relativeConvolutionRestriction_fibration (hq : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations R q.hom) :
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations R (relativeConvolutionRestriction R q f).hom := by
  rw [relativeConvolutionRestriction_hom_eq]
  have h := _root_.SerrePositivity.ComplexLimits.complexPullbackHom_projectiveFibration
    ((EInfinity.BarrattEccles.normalizedFunctor R).map f) q.hom
    (_root_.SerrePositivity.ComplexLimits.normalizedMonomorphism_cofibration R f) hq
  intro n
  change Function.Surjective
    ((_root_.SerrePositivity.ComplexLimits.complexPullbackHom
      ((EInfinity.BarrattEccles.normalizedFunctor R).map f) q.hom).f n ≫
        (relativeConvolutionRestrictionUnderlyingIso R q f).inv.f n)
  exact ((ModuleCat.epi_iff_surjective _).mp (inferInstance :
    Epi ((relativeConvolutionRestrictionUnderlyingIso R q f).inv.f n))).comp (h n)

lemma relativeConvolutionRestriction_quasiIso
    (hf : QuasiIso ((EInfinity.BarrattEccles.normalizedFunctor R).map f)) :
    QuasiIso (relativeConvolutionRestriction R q f).hom := by
  rw [relativeConvolutionRestriction_hom_eq]
  have := _root_.SerrePositivity.ComplexLimits.complexPullbackHom_quasiIso
    ((EInfinity.BarrattEccles.normalizedFunctor R).map f) q.hom
    (_root_.SerrePositivity.ComplexLimits.normalizedMonomorphism_cofibration R f) hf
  infer_instance

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
