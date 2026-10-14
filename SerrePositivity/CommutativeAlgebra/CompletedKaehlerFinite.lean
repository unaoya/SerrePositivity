module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionFinite
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # 有限型の閉ファイバーから完備微分の有限性へ

余接の右完全列で通常の微分のイデアル商の有限性を証明し、完備化へ移す。
通常の微分自体の有限生成性・Noether性・体・標数は要求しない。
-/

@[expose] public section
namespace SerrePositivity
variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]

/-- 有限生成イデアルの閉ファイバーが有限型なら、通常の微分のイデアル商は有限。 -/
theorem moduleFinite_kaehler_quotient_of_finiteType_fiber
    (I : Ideal S) (hI : I.FG) [Algebra.EssFiniteType k (S ⧸ I)] :
    Module.Finite S
      (KaehlerDifferential k S ⧸ I • (⊤ : Submodule S (KaehlerDifferential k S))) := by
  let Q := S ⧸ I
  let K := RingHom.ker (algebraMap S Q)
  have hK : K.FG := by
    simpa only [K, Q, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] using hI
  let : Module.Finite S K := Module.Finite.of_fg hK
  let : Module.Finite S K.Cotangent :=
    Module.Finite.of_surjective K.toCotangent K.toCotangent_surjective
  let : Module.Finite S (KaehlerDifferential k Q) := Module.Finite.trans Q _
  have hs : Function.Surjective (algebraMap S Q) := Ideal.Quotient.mk_surjective
  let : Module.Finite S (TensorProduct S Q (KaehlerDifferential k S)) :=
    Module.Finite.of_exact
      (f := KaehlerDifferential.kerCotangentToTensor k S Q)
      (g := (KaehlerDifferential.mapBaseChange k S Q).restrictScalars S)
      (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k S Q hs)
      (KaehlerDifferential.mapBaseChange_surjective k S Q hs)
  exact Module.Finite.of_surjective
    (TensorProduct.quotTensorEquivQuotSMul (KaehlerDifferential k S) I).toLinearMap
    (TensorProduct.quotTensorEquivQuotSMul (KaehlerDifferential k S) I).surjective

/-- 有限型の閉ファイバーと基底の前完備性から完備微分の有限性を得る。 -/
theorem moduleFinite_completedKaehler_of_finiteType_fiber
    (I : Ideal S) (hI : I.FG) [IsPrecomplete I S] [Algebra.EssFiniteType k (S ⧸ I)] :
    Module.Finite S (AdicCompletion I (KaehlerDifferential k S)) := by
  let : Module.Finite S
      (KaehlerDifferential k S ⧸ I • (⊤ : Submodule S (KaehlerDifferential k S))) :=
    moduleFinite_kaehler_quotient_of_finiteType_fiber I hI
  exact moduleFinite_adicCompletion_of_finite_quotient I hI

end SerrePositivity
