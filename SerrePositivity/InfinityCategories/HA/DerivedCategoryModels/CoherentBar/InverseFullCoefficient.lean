module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseFullDifferential
/-!
概要：逆構成の全頂点成分を、全パラメーター係数と native 列の実合成へ同定する。
方針：左右の全頂点集合を矩形因数分解へ代入する。
規約：余錐族の存在も HA 方程式も仮定しない。
使われ方：逆構成の全頂点 HA 方程式。
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
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

def dgCoherentBarInverseFullColumn {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) : GradedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩) N
      (-((n + m : ℕ) : ℤ)) :=
  compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)
    (y := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) (z := N)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFullHom R D F hMC N f)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
    (show -(n : ℤ) + -(m : ℤ) = -((n + m : ℕ) : ℤ) by omega)

lemma dgCoherentBarInverseRawData_full_hom_heq {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    HEq ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s).hom Finset.univ
      0 (Fin.last (n + m + 1)) (-((n + m : ℕ) : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card (n + m)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (n + m))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (n + m)) (by simp; omega))
      (dgCoherentBarInverseFullColumn R D F hMC N f s) := by
  let T := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s
  have hSet := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_univ n m
  have hJ : 2 ≤ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset
      (Finset.univ : Finset (Fin (n + 1))) (Finset.univ : Finset (Fin (m + 1)))).card := by
    rw [hSet]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card (n + m)
  have ha : (0 : Fin (n + m + 1 + 1)) = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset
      (Finset.univ : Finset (Fin (n + 1)))
      (Finset.univ : Finset (Fin (m + 1)))).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) := by
    simpa only [hSet] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (n + m)
  have hb : Fin.last (n + m + 1) = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset
      (Finset.univ : Finset (Fin (n + 1)))
      (Finset.univ : Finset (Fin (m + 1)))).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) := by
    simpa only [hSet] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (n + m)
  have hk : -((n + m : ℕ) : ℤ) = 2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset
      (Finset.univ : Finset (Fin (n + 1))) (Finset.univ : Finset (Fin (m + 1)))).card : ℤ) := by
    rw [hSet]
    simp
    omega
  have hRaw := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_mixed_hom_heq R D F hMC N f s
    Finset.univ Finset.univ Finset.univ_nonempty Finset.univ_nonempty n (by simp)
    (-(m : ℤ)) (by simp) 0 (Fin.last (n + m + 1)) (-((n + m : ℕ) : ℤ)) hJ ha hb hk
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel_univ] at hRaw
  have hIndex := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree T hSet.symm rfl rfl rfl
    (k := -((n + m : ℕ) : ℤ)) (l := -((n + m : ℕ) : ℤ))
    (hI := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card (n + m))
    (ha := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (n + m)) (hb := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (n + m))
    (hk := by simp; omega) (hJ := hJ) (hc := ha) (hd := hb) (hl := hk)
  refine hIndex.trans (hRaw.trans ?_)
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_compose_degree_heq (R := R)
    (a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩) (b := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
    (c := N) (p := -(n : ℤ)) (q := -(m : ℤ))
    (k := -(m : ℤ) - (n : ℤ)) (l := -((n + m : ℕ) : ℤ))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFullHom R D F hMC N f)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩) (by omega) (by omega)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
