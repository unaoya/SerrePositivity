module

public import SerrePositivity.EInfinity.PowerOperation.MayRepeatedCycles

/-!
# 零次の May 演算の単位射での評価

May, Proposition 2.3(iii) の零次計算を指定 D_i の値と比べるための補助。
単位複体の同じ指定元と、元のテンソル複体の左単位同型を使う。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {k : Type u} [CommRing k]

lemma mayUnitLeftInverse_value (K : Complex k) (q : ℤ) (a : K.X q) :
    (λ_ K).inv.f q a =
      ιTensorObj (𝟙_ (Complex k)) K 0 q q (zero_add q)
        (mayTensorUnitValue (k := k) ⊗ₜ[k] a) := by
  change (HomologicalComplex.leftUnitor' K).inv q a = _
  rw [HomologicalComplex.leftUnitor'_inv]
  rfl

end SerrePositivity.EInfinity.PowerOperation
