module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateUnit
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.DegeneracyOperators
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarFaceDifferential
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateFaceCoefficients
/-!
概要：最初の退化 prefix の実 Hom 係数を、同じ始点加群の単位へ照合する。
方針：prefix ラベルの退化辺表示と、既存の端点輸送の異種等号を合成する。
規約：同じ元の加群・次数・shift ブロックを保持する。
使われ方：退化位置零での面項と prefix 項の係数相殺。
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

lemma dgCoherentBarPrefixHom_first_degenerate_unit {n : ℕ} (s : I _⦋n⦌) :
    HEq (dgCoherentBarPrefixHom R D F (I.σ 0 s) 0 (by omega))
      (unitElement R (dgCoherentBarSource R D F ⟨n + 1, I.σ 0 s⟩)).val := by
  have hx : dgCoherentBarSource R D F ⟨n + 1, I.σ 0 s⟩ =
      coherentDiagramVertex F (I.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op s) :=
    dgCoherentBarSource_degeneracy R D F s 0
  have htop : HEq (coherentDiagramTop F
      (dgCoherentBarPrefix (I.σ 0 s) 1 (by omega)).2)
      (unitElement R (dgCoherentBarSource R D F ⟨n + 1, I.σ 0 s⟩)).val := by
    rw [dgCoherentBarPrefix_degeneracy_zero, hx]
    exact dgCoherentBar_native_degenerateEdge_unit_transported F _
  unfold dgCoherentBarPrefixHom
  exact (gradedHomTransport_heq _ _ _ _).trans htop

private lemma shiftBlock_heq (s t : ℤ) (M N N' : RightModule R D) (hN : N = N')
    {q k : ℤ} (f : (moduleHom R D M N).X q) (g : (moduleHom R D M N').X q)
    (hfg : HEq f g) (hk : s + q - t = k) :
    HEq (moduleHomShiftBlock R D s t f hk) (moduleHomShiftBlock R D s t g hk) := by
  cases hN
  cases hfg
  rfl

lemma dgCoherentBarPrefixBlock_first_degenerate_unit {n : ℕ} (s : I _⦋n⦌) :
    HEq (dgCoherentBarPrefixBlock R D F (I.σ 0 s) 0 (by omega))
      (moduleHomShiftBlock R D ((n + 1 : ℕ) : ℤ) (n : ℤ)
        (unitElement R (dgCoherentBarSource R D F ⟨n + 1, I.σ 0 s⟩)).val
          (by omega : ((n + 1 : ℕ) : ℤ) + 0 - (n : ℤ) = 1)) := by
  have hsrc : dgCoherentBarSource R D F (dgCoherentBarTail (I.σ 0 s) 1 (by omega)) =
      dgCoherentBarSource R D F ⟨n + 1, I.σ 0 s⟩ := by
    rw [dgCoherentBarTail_degeneracy_zero]
    exact (dgCoherentBarSource_degeneracy R D F s 0).symm
  unfold dgCoherentBarPrefixBlock
  exact shiftBlock_heq R D ((n + 1 : ℕ) : ℤ) (n : ℤ) _ _ _ hsrc
    (dgCoherentBarPrefixHom R D F (I.σ 0 s) 0 (by omega))
    (unitElement R (dgCoherentBarSource R D F ⟨n + 1, I.σ 0 s⟩)).val
    (dgCoherentBarPrefixHom_first_degenerate_unit R D F s) (by omega)

set_option maxHeartbeats 800000 in
-- 二つの端点輸送付きブロックを同じ直和包含へ送るための局所上限。
lemma dgCoherentBarPrefixColumn_first_degenerate_eq_face {n : ℕ} (s : I _⦋n⦌) :
    dgCoherentBarPrefixColumn R D F (I.σ 0 s) 0 (by omega) =
      dgCoherentBarFaceColumn R D F (I.σ 0 s) 0 := by
  have hlabel : dgCoherentBarTail (I.σ 0 s) 1 (by omega) =
      dgCoherentBarFace (I.σ 0 s) (0 : Fin (n + 1)).succ := by
    rw [dgCoherentBarTail_degeneracy_zero]
    simp only [dgCoherentBarFace, I.δ_comp_σ_succ_apply]
  exact dgCoherentBarPostInclusion_eq_of_heq R D F ⟨n + 1, I.σ 0 s⟩
    (dgCoherentBarTail (I.σ 0 s) 1 (by omega))
    (dgCoherentBarFace (I.σ 0 s) (0 : Fin (n + 1)).succ) hlabel 1
    (dgCoherentBarPrefixBlock R D F (I.σ 0 s) 0 (by omega))
    (dgCoherentBarFaceBlock R D F (I.σ 0 s) 0)
    ((dgCoherentBarPrefixBlock_first_degenerate_unit R D F s).trans
      (dgCoherentBarFaceBlock_heq R D F (I.σ 0 s) 0).symm)

end SerrePositivity.InfinityCategories
