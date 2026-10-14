module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionExt
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # 二つのイデアルに沿う完備化の比較

各完備化が相手のイデアルについても完備なら、元の加群の像を保つ自然な同型がある。
有限生成イデアルの完備化の外延性を使い、元の加群の有限性は要求しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- J進完備化がI進完備なら、元の加群の像を保つI進完備化からの自然な写像。 -/
def adicCompletionChangeIdealMap (I J : Ideal R) [IsAdicComplete I (AdicCompletion J M)] :
    AdicCompletion I M →ₗ[R] AdicCompletion J M :=
  (AdicCompletion.ofLinearEquiv I (AdicCompletion J M)).symm.toLinearMap.comp
    ((AdicCompletion.map I (AdicCompletion.of J M)).restrictScalars R)

@[simp] theorem adicCompletionChangeIdealMap_of (I J : Ideal R)
    [IsAdicComplete I (AdicCompletion J M)] (m : M) :
    adicCompletionChangeIdealMap I J (AdicCompletion.of I M m) = AdicCompletion.of J M m := by
  change (AdicCompletion.ofLinearEquiv I (AdicCompletion J M)).symm
    (AdicCompletion.map I (AdicCompletion.of J M) (AdicCompletion.of I M m)) = _
  rw [AdicCompletion.map_of, AdicCompletion.ofLinearEquiv_symm_of]

/-- 互いのイデアルについて完備な二つの完備化を、元の加群の像を保って同定する。 -/
def adicCompletionChangeIdealEquiv (I J : Ideal R) (hI : I.FG) (hJ : J.FG)
    [IsAdicComplete I (AdicCompletion J M)] [IsAdicComplete J (AdicCompletion I M)] :
    AdicCompletion I M ≃ₗ[R] AdicCompletion J M := by
  let : IsAdicComplete I (AdicCompletion I M) := AdicCompletion.isAdicComplete hI
  let : IsAdicComplete J (AdicCompletion J M) := AdicCompletion.isAdicComplete hJ
  let f := adicCompletionChangeIdealMap (M := M) I J
  let g := adicCompletionChangeIdealMap (M := M) J I
  have hfg : f.comp g = LinearMap.id := by
    apply adicCompletion_linearMap_ext_of_of J hJ
    ext m
    simp [f, g]
  have hgf : g.comp f = LinearMap.id := by
    apply adicCompletion_linearMap_ext_of_of I hI
    ext m
    simp [f, g]
  exact LinearEquiv.ofLinearMap f g hfg hgf

@[simp] theorem adicCompletionChangeIdealEquiv_of (I J : Ideal R) (hI : I.FG) (hJ : J.FG)
    [IsAdicComplete I (AdicCompletion J M)] [IsAdicComplete J (AdicCompletion I M)] (m : M) :
    adicCompletionChangeIdealEquiv I J hI hJ (AdicCompletion.of I M m) =
      AdicCompletion.of J M m :=
  adicCompletionChangeIdealMap_of I J m

end SerrePositivity
