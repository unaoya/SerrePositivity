module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerComponentComposition

/-!
概要：零底と層の実代数 pro 逆を、作用を保つ係数逆と四つの厳密な三角形へ移す。
方針：同じ実逆の成分を抽出し、合成則で元の二三角形を成分ごとに回収する。
規約：底・係数を別々に選ばない。使われ方：元の roof の零切断との一致。
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
variable (R : Type u) [CommRing R] (n : ℤ)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)

structure PostnikovZeroLayerInverse (i k : ℕ) (hi : i ≤ k) where
  base : postnikov R (B.obj k).obj 0 ⟶ postnikov R (A.obj i).obj 0
  coefficient : postnikovLayerZeroBimodule R (B.obj k).obj n ⟶
    bimoduleRestrict base (postnikovLayerZeroBimodule R (A.obj i).obj n)
  left_base : postnikovMap R (f.app k).hom 0 ≫ base =
    postnikovMap R (A.transition hi).hom 0
  right_base : base ≫ postnikovMap R (f.app i).hom 0 =
    postnikovMap R (B.transition hi).hom 0
  left_coefficient : postnikovLayerMap R (f.app k).hom n ≫ coefficient.hom =
    postnikovLayerMap R (A.transition hi).hom n
  right_coefficient : coefficient.hom ≫ postnikovLayerMap R (f.app i).hom n =
    postnikovLayerMap R (B.transition hi).hom n

namespace PostnikovZeroLayerInverse
variable (hn : 0 ≤ n) {i k : ℕ} {hi : i ≤ k}
  (r : postnikovZeroLayerAlgebra R (B.obj k).obj n ⟶
    postnikovZeroLayerAlgebra R (A.obj i).obj n)
  (hl : postnikovZeroLayerAlgebraMap R n (f.app k).hom ≫ r =
    postnikovZeroLayerAlgebraMap R n (A.transition hi).hom)
  (hr : r ≫ postnikovZeroLayerAlgebraMap R n (f.app i).hom =
    postnikovZeroLayerAlgebraMap R n (B.transition hi).hom)

def ofAlgebraInverse : PostnikovZeroLayerInverse R n f i k hi where
  base := postnikovZeroLayerHomBase R n r
  coefficient := postnikovZeroLayerHomBimoduleMap R n r hn
  left_base := by
    have he := congrArg (fun t => postnikovZeroLayerHomBase R n t) hl
    rw [postnikovZeroLayerHomBase_comp R n hn, postnikovZeroLayerHomBase_of_map,
      postnikovZeroLayerHomBase_of_map] at he
    exact he
  right_base := by
    have he := congrArg (fun t => postnikovZeroLayerHomBase R n t) hr
    rw [postnikovZeroLayerHomBase_comp R n hn, postnikovZeroLayerHomBase_of_map,
      postnikovZeroLayerHomBase_of_map] at he
    exact he
  left_coefficient := by
    have he := congrArg (fun t => postnikovZeroLayerHomCoefficient R n t) hl
    rw [postnikovZeroLayerHomCoefficient_comp R n hn, postnikovZeroLayerHomCoefficient_of_map,
      postnikovZeroLayerHomCoefficient_of_map] at he
    exact he
  right_coefficient := by
    have he := congrArg (fun t => postnikovZeroLayerHomCoefficient R n t) hr
    rw [postnikovZeroLayerHomCoefficient_comp R n hn, postnikovZeroLayerHomCoefficient_of_map,
      postnikovZeroLayerHomCoefficient_of_map] at he
    exact he

end PostnikovZeroLayerInverse

lemma exists_postnikovZeroLayerInverse_after (hn : 0 ≤ n)
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (hₙ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R (n + 1)))) (i bound : ℕ) :
    ∃ k, ∃ hi : i ≤ k, bound ≤ k ∧ Nonempty (PostnikovZeroLayerInverse R n f i k hi) := by
  obtain ⟨k, hi, hb, r, hl, hr⟩ :=
    exists_postnikovZeroLayerAlgebraInverse_after R n f h₀ hₙ i bound
  exact ⟨k, hi, hb, ⟨PostnikovZeroLayerInverse.ofAlgebraInverse R n f hn r hl hr⟩⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
