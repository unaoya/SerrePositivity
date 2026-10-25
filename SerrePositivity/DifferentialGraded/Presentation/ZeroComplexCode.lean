module
public import SerrePositivity.DifferentialGraded.Presentation.ComplexCode
public import Mathlib.LinearAlgebra.Quotient.Basic
/-!
概要：固定基底の全関係による零複体の提示コードを構成する。
方針：各次数を自由加群の全部分加群で割り、微分を零にする。
規約：台の型を変更せず、既存の小さい提示型を使う。
使われ方：出発提示の非連結和で異なる成分間の Hom を零にする。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (R : Type u) [CommRing R] (B : Type u)

namespace DGComplexPresentationCode

def zero : DGComplexPresentationCode R B where
  relations _ := ⊤
  differential _ := 0
  square _ := zero_comp

lemma zero_value_isZero : IsZero ((zero R B).value R B) := by
  apply (IsZero.iff_id_eq_zero _).2
  ext n x
  change (x : (B →₀ R) ⧸ (⊤ : Submodule R (B →₀ R))) = 0
  exact @Subsingleton.elim ((B →₀ R) ⧸ (⊤ : Submodule R (B →₀ R)))
    ((Submodule.Quotient.subsingleton_iff).2 rfl) x 0

end DGComplexPresentationCode
end SerrePositivity.DifferentialGraded
