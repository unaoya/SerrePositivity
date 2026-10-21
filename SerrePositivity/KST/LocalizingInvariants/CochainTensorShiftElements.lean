module

public import SerrePositivity.HomologicalAlgebra.CochainTensorShift
public import SerrePositivity.HomologicalAlgebra.CochainTensorTriple

/-!
概要：tensor–shift 同型を、再添字付けした斉次元と明示的な符号で計算する。
方針：既存の全成分式を元へ適用し、同じ次数の標準同型を消す。
規約：右因子 shift の Koszul 符号を保持。使われ方：双加群 shift の coherence。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R]

lemma tensorShiftLeft_apply (P Q : CochainComplex (ModuleCat R) ℤ) (s i j n : ℤ)
    (h : i + j = n) (x : P.X (i + s)) (y : Q.X j) :
    (cochainTensorShiftLeft P Q s).hom.f n
      (ιTensorObj (P⟦s⟧) Q i j n h (x ⊗ₜ[R] y)) =
    ιTensorObj P Q (i + s) j (n + s) (by omega) (x ⊗ₜ[R] y) := by
  have he := congrArg (fun f ↦ f (x ⊗ₜ[R] y))
    (ιTensorObj_cochainTensorShiftLeft P Q s i j n h)
  simpa [CochainComplex.shiftFunctorObjXIso] using he

lemma tensorShiftRight_apply (P Q : CochainComplex (ModuleCat R) ℤ) (s i j n : ℤ)
    (h : i + j = n) (x : P.X i) (y : Q.X (j + s)) :
    (cochainTensorShiftRight P Q s).hom.f n
      (ιTensorObj P (Q⟦s⟧) i j n h (x ⊗ₜ[R] y)) =
    (i * s).negOnePow • ιTensorObj P Q i (j + s) (n + s) (by omega) (x ⊗ₜ[R] y) := by
  have he := congrArg (fun f ↦ f (x ⊗ₜ[R] y))
    (ιTensorObj_cochainTensorShiftRight P Q s i j n h)
  simpa [CochainComplex.shiftFunctorObjXIso] using he

end SerrePositivity.KST.LocalizingInvariants
