module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovOneRoofZeroLeft
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerInverseComponents

/-!
概要：作用を保つ係数逆の実底成分を、元の一切断 roof の零切断の逆と後続段で揃える。
方針：元の零切断射の pro 同型と、両底射の元の左三角形に eventual 一意性を適用する。
規約：元の二つの逆を選び直さない。使われ方：細分した共通底への係数逆の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)

lemma postnikovZeroLayerInverse_base_eventually_roof
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    {n : ℤ} {l : ℕ} {hj : i ≤ l} (e : PostnikovZeroLayerInverse R n f i l hj) :
    ∃ k, ∃ hm : m ≤ k, ∃ hl : l ≤ k,
      postnikovMap R (B.transition hm).hom 0 ≫ postnikovOneRoofZeroInverse R f c =
        postnikovMap R (B.transition hl).hom 0 ≫ e.base :=
  TowerDiagram.inverse_left_eventually_unique (f.map (postnikovFunctor R 0))
    (postnikovZeroMap_isProIso R f h₀) hi hj (postnikovOneRoofZeroInverse R f c) e.base
    (postnikovOneRoofZeroInverse_left R f c) e.left_base

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
