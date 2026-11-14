module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateUnit
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegeneracyOperators
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Faces.DGCoherentBarFaceDifferential
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateFaceCoefficients
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarPrefixHom_first_degenerate_unit {n : ℕ} (s : I _⦋n⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F (I.σ 0 s) 0 (by omega))
      (unitElement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, I.σ 0 s⟩)).val := by
  have hx : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, I.σ 0 s⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex F (I.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op s) :=
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarSource_degeneracy R D F s 0
  have htop : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop F
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix (I.σ 0 s) 1 (by omega)).2)
      (unitElement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, I.σ 0 s⟩)).val := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPrefix_degeneracy_zero, hx]
    exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBar_native_degenerateEdge_unit_transported F _
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ _ _).trans htop

private lemma shiftBlock_heq (s t : ℤ) (M N N' : _root_.SerrePositivity.DifferentialGraded.RightModule R D) (hN : N = N')
    {q k : ℤ} (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M N).X q) (g : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M N').X q)
    (hfg : HEq f g) (hk : s + q - t = k) :
    HEq (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D s t f hk) (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D s t g hk) := by
  cases hN
  cases hfg
  rfl

lemma dgCoherentBarPrefixBlock_first_degenerate_unit {n : ℕ} (s : I _⦋n⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D F (I.σ 0 s) 0 (by omega))
      (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D ((n + 1 : ℕ) : ℤ) (n : ℤ)
        (unitElement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, I.σ 0 s⟩)).val
          (by omega : ((n + 1 : ℕ) : ℤ) + 0 - (n : ℤ) = 1)) := by
  have hsrc : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail (I.σ 0 s) 1 (by omega)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, I.σ 0 s⟩ := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarTail_degeneracy_zero]
    exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarSource_degeneracy R D F s 0).symm
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock
  exact shiftBlock_heq R D ((n + 1 : ℕ) : ℤ) (n : ℤ) _ _ _ hsrc
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F (I.σ 0 s) 0 (by omega))
    (unitElement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, I.σ 0 s⟩)).val
    (dgCoherentBarPrefixHom_first_degenerate_unit R D F s) (by omega)

set_option maxHeartbeats 800000 in
-- 二つの端点輸送付きブロックを同じ直和包含へ送るための局所上限。
lemma dgCoherentBarPrefixColumn_first_degenerate_eq_face {n : ℕ} (s : I _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D F (I.σ 0 s) 0 (by omega) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F (I.σ 0 s) 0 := by
  have hlabel : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail (I.σ 0 s) 1 (by omega) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace (I.σ 0 s) (0 : Fin (n + 1)).succ := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarTail_degeneracy_zero]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace, I.δ_comp_σ_succ_apply]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPostInclusion_eq_of_heq R D F ⟨n + 1, I.σ 0 s⟩
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail (I.σ 0 s) 1 (by omega))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace (I.σ 0 s) (0 : Fin (n + 1)).succ) hlabel 1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D F (I.σ 0 s) 0 (by omega))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D F (I.σ 0 s) 0)
    ((dgCoherentBarPrefixBlock_first_degenerate_unit R D F s).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock_heq R D F (I.σ 0 s) 0).symm)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
