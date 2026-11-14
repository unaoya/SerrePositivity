module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.AffineEnvelopePointwiseCoefficients
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensorExt
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.AffineEnvelopePointwiseCoefficients
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.TensorCompletionUnit
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange

/-!
# 有限 affine Čech 模型の各項の完備係数比較

## 概要
結晶的な係数への有限 affine 項の同型を、余単体的加群の同型に組み立てる。

## 方針
各項の左右の脚を固定した同型と、既存の affine 係数射の厳密な自然性を使う。

## 規約
両基底は有界 prism、終域の生成元は p。導来底変換との各項の比較は別の離散性に依る。

## 使われ方
BS 著者版 Theorem 6.4、結晶の橋の係数変更。
-/

public noncomputable section
open CategoryTheory
open scoped TensorProduct ChangeOfRings Simplicial
open SerrePositivity.DerivedCompletion
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (Q : OrientedPrism p B)
variable (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (hg : Q.generator = (p : B))
variable (f : OrientedPrism.Hom P Q) (r : ℕ)

private abbrev sourceTerm (n : ℕ) :=
  affineEnvelopeTerm P hP r n (cutoff A (prismPolynomialCompletion P (Fin r))) le_rfl
private abbrev targetTerm (n : ℕ) :=
  affineEnvelopeTerm Q hQ r n (cutoff B (prismPolynomialCompletion Q (Fin r))) le_rfl

private def component (n : ℕ) :
    letI := f.toRingHom.toAlgebra
    letI := (sourceTerm P hP r n).X.toHom.toRingHom.toAlgebra
    letI := (targetTerm Q hQ r n).X.toHom.toRingHom.toAlgebra
    (pCompletedScalarExtensionFunctor p f.toRingHom).obj
      (ModuleCat.of A (sourceTerm P hP r n).X.B) ≅
      ModuleCat.of B (targetTerm Q hQ r n).X.B :=
  affineEnvelopePointwiseCoefficientIso P Q hP hQ hg f r n _ _ le_rfl le_rfl

private theorem component_unit (n : ℕ) (b : B) (x : (sourceTerm P hP r n).X.B) :
    letI := f.toRingHom.toAlgebra
    letI := (sourceTerm P hP r n).X.toHom.toRingHom.toAlgebra
    letI := (targetTerm Q hQ r n).X.toHom.toRingHom.toAlgebra
    (component P Q hP hQ hg f r n).hom
      (((moduleCompletionH0Unit B (p : B)).app
        ((ModuleCat.extendScalars f.toRingHom).obj
          (ModuleCat.of A (sourceTerm P hP r n).X.B))) (b ⊗ₜ[A,f.toRingHom] x)) =
      b • affineEnvelopeCoefficientMap f (sourceTerm P hP r n) (targetTerm Q hQ r n) x := by
  let := f.toRingHom.toAlgebra
  let := (sourceTerm P hP r n).X.toHom.toRingHom.toAlgebra
  let := (targetTerm Q hQ r n).X.toHom.toRingHom.toAlgebra
  let U := sourceTerm P hP r n
  let V := targetTerm Q hQ r n
  let e := affineEnvelopeCompletedTensorAlgEquiv P Q hP hQ hg f r n _ _ le_rfl le_rfl
  change e ((pCompletedScalarExtensionTensorIso p A B U.X.B).hom _) = _
  have ht := pCompletedScalarExtensionTensorIso_unit p A B U.X.B b x
  refine (congrArg e ht).trans ?_
  let L : B ⊗[A] U.X.B →ₗ[B] V.X.B := e.toLinearMap.comp
    (TensorCompletionUnit.unitAlg p B (B ⊗[A] U.X.B)).toLinearMap
  have hb : (b ⊗ₜ[A] x : B ⊗[A] U.X.B) = b • ((1 : B) ⊗ₜ[A] x) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  change L (b ⊗ₜ[A] x) = _
  rw [hb, L.map_smul]
  exact congrArg (b • ·)
    (affineEnvelopeCompletedTensorRingEquiv_right P Q hP hQ hg f r n _ _ le_rfl le_rfl x)

private theorem target_complete (n : ℕ) :
    letI := (targetTerm Q hQ r n).X.toHom.toRingHom.toAlgebra
    IsModuleComplete B (p : B) (ModuleCat.of B (targetTerm Q hQ r n).X.B) := by
  let V := targetTerm Q hQ r n
  let := V.X.toHom.toRingHom.toAlgebra
  apply (isModuleComplete_algebraMap_iff B V.X.B (p : B) V.X.B).mp
  rw [map_natCast]
  exact V.X.Q.complete_p

/-- 有限 affine Čech 模型の完備係数比較は、余単体的加群の同型になる。 -/
def affineCechPointwiseCoefficientIso :
    SerrePositivity.Cosimplicial.toModules A (htRings P hP r) (htBase P hP r) ⋙
        pCompletedScalarExtensionFunctor p f.toRingHom ≅
      SerrePositivity.Cosimplicial.toModules B (htRings Q hQ r) (htBase Q hQ r) := by
  let := f.toRingHom.toAlgebra
  refine NatIso.ofComponents (fun n => component P Q hP hQ hg f r n.len) ?_
  intro m n θ
  obtain ⟨m⟩ := m
  obtain ⟨n⟩ := n
  let Um := sourceTerm P hP r m
  let Un := sourceTerm P hP r n
  let Vm := targetTerm Q hQ r m
  let Vn := targetTerm Q hQ r n
  let := Um.X.toHom.toRingHom.toAlgebra
  let := Un.X.toHom.toRingHom.toAlgebra
  let := Vm.X.toHom.toRingHom.toAlgebra
  let := Vn.X.toHom.toRingHom.toAlgebra
  apply pCompletedScalarExtension_hom_ext p A B Um.X.B (ModuleCat.of B Vn.X.B)
    (target_complete Q hQ r n)
  intro b x
  change (component P Q hP hQ hg f r n).hom
      ((pCompletedScalarExtensionFunctor p f.toRingHom).map
        ((SerrePositivity.Cosimplicial.toModules A (htRings P hP r) (htBase P hP r)).map θ) _) =
    (SerrePositivity.Cosimplicial.toModules B (htRings Q hQ r) (htBase Q hQ r)).map θ
      ((component P Q hP hQ hg f r m).hom _)
  have hu := pCompletedScalarExtension_map_unit_linear p A B
    ((SerrePositivity.Cosimplicial.toModules A (htRings P hP r) (htBase P hP r)).map θ) b x
  refine (congrArg (component P Q hP hQ hg f r n).hom hu).trans ?_
  refine (component_unit P Q hP hQ hg f r n b
    ((SerrePositivity.Cosimplicial.toModules A (htRings P hP r) (htBase P hP r)).map θ x)).trans ?_
  have hc := RingHom.congr_fun (affineEnvelopeCoefficientMap_natural f Un Vn Um Vm θ) x
  have hr := congrArg
    ((SerrePositivity.Cosimplicial.toModules B (htRings Q hQ r) (htBase Q hQ r)).map θ)
      (component_unit P Q hP hQ hg f r m b x)
  refine (congrArg (b • ·) hc).trans ?_
  exact (map_smul
    ((SerrePositivity.Cosimplicial.toModules B (htRings Q hQ r) (htBase Q hQ r)).map θ).hom b
      (affineEnvelopeCoefficientMap f Um Vm x)).symm.trans hr.symm

end SerrePositivity.BhattScholze.Prismatic
