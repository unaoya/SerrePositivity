module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseKoszulCompletion
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# 係数環上で自由な関係商の完備化後の Koszul 正則性

## 概要
係数環上で自由な代数と自由な通常商を持つ Koszul 分解は、実 H⁰ 主完備化の後でも分解になる。
## 方針
係数環へ制限した両模型を K-projective とし、各項完備化が保つホモトピー同値を使う。
既存の各項完備化の比較で、完備環上の実際の Koszul 複体へ戻す。
## 規約
BS 著者版 Proposition 7.10 の有限 T。係数環上の p 正則性を仮定しない。
## 使われ方
根付き変数の有限関係の実完備化への移送。
-/

public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (p : ℕ)

/-- 概要：係数環上で自由な代数と自由な関係商の Koszul 分解は実主完備化で保たれる。
方針：K-projective な模型のホモトピー同値を各項完備化し、標準の複体比較を通す。
規約：BS 著者版 Proposition 7.10 の有限 T に用いる。p の正則性・非零性は不要。
使われ方：完備な根付き基底の Xi−fi の Koszul 正則性。 -/
theorem completedKoszul_isKoszulResolution {r : ℕ} (z : Fin r → A)
    (hz : IsKoszulResolution z) [Module.Free R A]
    [Module.Free R (A ⧸ Ideal.span (Set.range z))] :
    IsKoszulResolution ((principalCompletionRingCatUnit p (CommRingCat.of A)).hom ∘ z) := by
  let φ := algebraMap R A
  let Res := ModuleCat.restrictScalars φ
  let ResC := Res.mapHomologicalComplex (.up ℤ)
  let Q := A ⧸ Ideal.span (Set.range z)
  let K : CochainComplex (ModuleCat.{u} R) ℤ := ResC.obj (koszulComplex z)
  let L : CochainComplex (ModuleCat.{u} R) ℤ := (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj (ModuleCat.of R Q)
  let eQ : Res.obj (ModuleCat.of A Q) ≅ ModuleCat.of R Q :=
    LinearEquiv.toModuleIso <|
      @AddEquiv.toLinearEquiv R Q Q _ _ _
        (Res.obj (ModuleCat.of A Q)).isModule (ModuleCat.of R Q).isModule
        (AddEquiv.refl Q) (fun c x => by
          change (algebraMap R A c) • x = _
          exact algebraMap_smul A c x)
  let q : K ⟶ L := ResC.map (koszulAugmentation hz) ≫
    ((HomologicalComplex.singleMapHomologicalComplex Res (c := .up ℤ) 0).app (ModuleCat.of A Q)).hom ≫
    (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).map eQ.hom
  letI : QuasiIso q := by dsimp [q]; infer_instance
  letI (i : ℤ) : Module.Free R (K.X i) := by
    letI : Module A (K.X i) := ((koszulComplex z).X i).isModule
    letI : Module.Free A (K.X i) := (koszulComplex_free_finite_X z i).1
    letI : IsScalarTower R A (K.X i) := ⟨fun c a x => by
      change (c • a) • x = (algebraMap R A c) • (a • x)
      rw [Algebra.smul_def, mul_smul]⟩
    exact Module.Free.trans (R := R) (S := A)
  letI (i : ℤ) : Projective (K.X i) := inferInstance
  letI : K.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff K 0).mpr (fun i hi =>
    Res.map_isZero (koszulComplex_isZero_X_of_pos z i hi))
  letI : K.IsKProjective := CochainComplex.isKProjective_of_projective K 0
  letI (i : ℤ) : Projective (L.X i) := by dsimp [L]; infer_instance
  letI : L.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff L 0).mpr (fun i hi =>
    HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R Q) i (by omega))
  letI : L.IsKProjective := CochainComplex.isKProjective_of_projective L 0
  let F := moduleCompletionH0Functor R (p : R)
  let FC := F.mapHomologicalComplex (.up ℤ)
  letI : QuasiIso (FC.map q) := moduleCompletionH0Functor_map_quasiIso_of_KProjective (p : R) q
  let eL : FC.obj L ≅ (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj
      (F.obj (ModuleCat.of R Q)) :=
    (HomologicalComplex.singleMapHomologicalComplex F (c := .up ℤ) 0).app (ModuleCat.of R Q)
  let ψ := (principalCompletionRingCatUnit p (CommRingCat.of A)).hom
  let ResA := ModuleCat.restrictScalars ψ
  let KC := koszulComplex (ψ ∘ z)
  let eK := pointwiseKoszulCompletionRestrictionIso p A φ z
  refine ⟨?_, koszulComplex_homology_zero_equiv (ψ ∘ z)⟩
  intro i hi
  have hL : IsZero ((FC.obj L).homology i) :=
    (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 (F.obj (ModuleCat.of R Q)) i hi).of_iso
      ((HomologicalComplex.homologyFunctor _ _ i).mapIso eL)
  have hK : IsZero ((FC.obj K).homology i) := hL.of_iso (asIso (HomologicalComplex.homologyMap (FC.map q) i))
  have hC : IsZero ((ResC.obj ((ResA.mapHomologicalComplex (.up ℤ)).obj KC)).homology i) :=
    hK.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso eK).symm
  let eH := (((ResA.mapHomologicalComplex (.up ℤ)).obj KC).sc i).mapHomologyIso Res ≪≫
    Res.mapIso ((KC.sc i).mapHomologyIso ResA)
  have hM : IsZero (Res.obj (ResA.obj (KC.homology i))) := hC.of_iso eH.symm
  have hSub := ModuleCat.subsingleton_of_isZero hM
  change Subsingleton (KC.homology i) at hSub
  exact ModuleCat.isZero_iff_subsingleton.mpr hSub

end SerrePositivity.DerivedCompletion
