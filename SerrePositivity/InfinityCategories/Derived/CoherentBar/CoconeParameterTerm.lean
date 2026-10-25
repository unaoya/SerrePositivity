module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterComposite
/-!
概要：パラメーター側の全 HA 項を、標準面の高次 Hom と native 列の係数で表示する。
方針：削除成分を面へ戻し、切断合成を最後の面だけにまとめる。
規約：最後の内部頂点にも同じ有限和の式を使う。
使われ方：混合 HA 右辺から標準面の符号付き境界を回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

def dgCoherentBarCoconeFaceColumn {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m + 1⦌) (s : I _⦋n⦌) (a : Fin (m + 2)) :
    GradedHom R (dgCoherentBarSource R D F ⟨n, s⟩)
      (dgNerve.vertexEquiv R (RightModule R D) y) (-((n + (m + 1) : ℕ) : ℤ) + 1) :=
  compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
    (y := dgCoherentBarNormalizedModule R D F hMC)
    (z := dgNerve.vertexEquiv R (RightModule R D) y)
    (dgCoherentBarCoconeFamilyHom R D F hMC y ((coconeMappingSpace F y).δ a c))
    (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
    (show -(n : ℤ) + -(m : ℤ) = -((n + (m + 1) : ℕ) : ℤ) + 1 by omega)

lemma dgCoherentBarCoconeFamilyFullComposite_parameter
    {m n : ℕ} (c : (coconeMappingSpace F y) _⦋m + 1⦌) (s : I _⦋n⦌) (j : Fin (m + 1)) :
    HEq (dgCoherentBarFullComposite
      (dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData (j.natAdd n))
      (if j = Fin.last m then dgCoherentBarCoconeFaceColumn R D F hMC y c s
        (Fin.last (m + 1)) else 0) := by
  classical
  by_cases hj : j = Fin.last m
  · subst j
    rw [ite_eq_left rfl]
    exact dgCoherentBarCoconeFamilyFullComposite_parameter_last R D F y hMC c s
  · rw [ite_eq_right hj, dgCoherentBarCoconeFamilyFullComposite_parameter_zero R D F y c s j hj]
    exact gradedHom_zero_heq (A := R) (D := RightModule R D)
      (dgCoherentBarCoconeFamilySimplex_source R D F y c s)
      (dgCoherentBarCoconeFamilySimplex_target R D F y c s) rfl

lemma dgCoherentBarCoconeFamilyFullTerm_parameter {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m + 1⦌) (s : I _⦋n⦌) (j : Fin (m + 1)) :
    HEq (dgCoherentBarFullTerm
      (dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData (j.natAdd n))
      ((((m + 1 : ℕ) : ℤ) - (j.val : ℤ)).negOnePow •
        (dgCoherentBarCoconeFaceColumn R D F hMC y c s j.castSucc -
          if j = Fin.last m then dgCoherentBarCoconeFaceColumn R D F hMC y c s
            (Fin.last (m + 1)) else 0)) := by
  rw [dgCoherentBarFullTerm_eq_composite, dgCoherentBarFullTerm_sign_right,
    dgCoherentBarFullTerm_sign]
  apply dgCoherentBarHom_units_smul_heq
    (dgCoherentBarCoconeFamilySimplex_source R D F y c s)
    (dgCoherentBarCoconeFamilySimplex_target R D F y c s) rfl
  apply gradedHom_sub_heq
    (dgCoherentBarCoconeFamilySimplex_source R D F y c s)
    (dgCoherentBarCoconeFamilySimplex_target R D F y c s) rfl
  · exact dgCoherentBarCoconeFamilyFullErase_parameter R D F hMC y c s j
  · exact dgCoherentBarCoconeFamilyFullComposite_parameter R D F hMC y c s j

end SerrePositivity.InfinityCategories
