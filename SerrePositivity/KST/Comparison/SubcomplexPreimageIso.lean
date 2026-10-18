module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# 包含の中の部分対象

概要：包含に沿う小さい部分対象の逆像を、元の部分対象と同定する。
方針：入れ子になった部分型を次数ごとに平坦化する。
規約：Segal 1974 Proposition 1.6 の面の表示の補助。
使われ方：標準単体の面を境界の部分対象として扱う。
-/

@[expose] public section
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory

/--
概要：大きい部分対象の包含に沿った小さい部分対象の逆像は元の部分対象と同型。
方針：二重の部分型を一重にする同値を自然同型にする。
規約：包含の証拠のみを使う厳密な同型。
使われ方：境界の面の標準単体表示。
-/
def subcomplexPreimageIsoOfLE {K : SSet.{u}} (A B : K.Subcomplex) (h : A ≤ B) :
    (A.preimage B.ι : SSet.{u}) ≅ (A : SSet.{u}) :=
  NatIso.ofComponents (fun d => Equiv.toIso
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, h d x.2⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (fun _ => rfl)

/--
概要：部分対象の平坦化の同型は周囲への包含と両立する。
方針：各次数で元の値が変わらないことを使う。
規約：射の等式としての両立。
使われ方：面の表示と標準単体の写像の同定。
-/
theorem subcomplexPreimageIsoOfLE_hom_ι {K : SSet.{u}} (A B : K.Subcomplex) (h : A ≤ B) :
    (subcomplexPreimageIsoOfLE A B h).hom ≫ A.ι = (A.preimage B.ι).ι ≫ B.ι := rfl

end SerrePositivity.KST.Comparison
