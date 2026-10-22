module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroProjection
public import SerrePositivity.KST.LocalizingInvariants.CochainSeparatedBounds

/-!
概要：零次数の底と負の集中係数の分裂平方零代数射を、元の対角二成分に分ける。
方針：交差成分を次数の分離で零とし、実直和の二包含で回収する。
規約：底成分は実代数射、係数成分は実 cochain 射。使われ方：作用を保つ係数逆の抽出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants

lemma cochainHom_eq_zero_of_reverse_bounds {R : Type u} [CommRing R] {P T : Complex R}
    (a b : ℤ) [P.IsStrictlyGE b] [T.IsStrictlyLE a] (hab : a < b) (f : P ⟶ T) : f = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i < b
  · exact (P.isZero_of_isStrictlyGE b i hi).eq_of_src _ _
  · exact (T.isZero_of_isStrictlyLE a i (by omega)).eq_of_tgt _ _

namespace SquareZero.SeparatedHom
variable {R : Type u} [CommRing R] {A B : Mon (Complex R)}
  (M : Bimod A A) (N : Bimod B B) (r : algebra A M ⟶ algebra B N)

def base : A ⟶ B := zeroSection A M ≫ r ≫ projection B N

def coefficient : M.X ⟶ N.X :=
  (biprod.inr : M.X ⟶ (algebra A M).X) ≫ r.hom ≫ biprod.snd

variable (d : ℤ) (hd : d < 0)
  [A.X.IsStrictlyGE 0] [B.X.IsStrictlyGE 0]
  [M.X.IsStrictlyLE d] [N.X.IsStrictlyLE d]

include hd in
lemma base_coefficient_zero :
    (biprod.inl : A.X ⟶ (algebra A M).X) ≫ r.hom ≫
      (biprod.snd : (algebra B N).X ⟶ N.X) = 0 :=
  cochainHom_eq_zero_of_reverse_bounds d 0 hd _

include hd in
lemma coefficient_base_zero :
    (biprod.inr : M.X ⟶ (algebra A M).X) ≫ r.hom ≫
      (biprod.fst : (algebra B N).X ⟶ B.X) = 0 :=
  cochainHom_eq_zero_of_bounds d 0 hd _

include hd in
lemma base_inclusion : (biprod.inl : A.X ⟶ (algebra A M).X) ≫ r.hom =
    (base M N r).hom ≫ (biprod.inl : B.X ⟶ (algebra B N).X) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.inl_fst, Category.comp_id]
    rfl
  · simp only [Category.assoc, biprod.inl_snd, comp_zero]
    exact base_coefficient_zero M N r d hd

include hd in
lemma coefficient_inclusion : (biprod.inr : M.X ⟶ (algebra A M).X) ≫ r.hom =
    coefficient M N r ≫ (biprod.inr : N.X ⟶ (algebra B N).X) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.inr_fst, comp_zero]
    exact coefficient_base_zero M N r d hd
  · simp only [Category.assoc, biprod.inr_snd, Category.comp_id]
    rfl

include hd in
lemma hom_diagonal : r.hom = Limits.biprod.map (base M N r).hom (coefficient M N r) := by
  apply biprod.hom_ext'
  · rw [biprod.inl_map]
    exact base_inclusion M N r d hd
  · rw [biprod.inr_map]
    exact coefficient_inclusion M N r d hd

end SquareZero.SeparatedHom
end SerrePositivity.KST.LocalizingInvariants
