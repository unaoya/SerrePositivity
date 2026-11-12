module

public import SerrePositivity.KST.Spectra.NullHomotopyDifferenceClass

/-!
概要：零ホモトピーの差の高次ホモトピー類の自然性。
方針：選んだ充填を後合成し、任意の充填による計算の式を使う。
規約：写像の下で充填の選び直しを暗黙に同一視しない。
使われ方：Goerss–Jardine VIII §1。塔の遷移による零ホモトピーの差の移送。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.NullHomotopyDifference

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : SSet.{u}} {x : X _⦋0⦌} {y : Y _⦋0⦌} {n : ℕ}
  {s : X.PtSimplex (n + 1) x} (f : X ⟶ Y) (hf : f.app _ x = y)

/-- 零ホモトピーを基点を保つ射で後合成する。 -/
def mapNull (R : PtSimplex.RelStruct .const s (Fin.last (n + 1))) :
    PtSimplex.RelStruct .const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex f hf s) (Fin.last (n + 1)) where
  map := R.map ≫ f
  δ_castSucc_map := by
    rw [← Category.assoc, R.δ_castSucc_map, RelativeMorphism.const_map, const_comp, hf]
    rfl
  δ_succ_map := by
    rw [← Category.assoc, R.δ_succ_map]
    rfl
  δ_map_of_lt j hj := by rw [← Category.assoc, R.δ_map_of_lt j hj, const_comp, hf]
  δ_map_of_gt j hj := by rw [← Category.assoc, R.δ_map_of_gt j hj, const_comp, hf]

/-- 差のホーンの各既知面は後合成と可換。 -/
lemma face_map (R S : PtSimplex.RelStruct .const s (Fin.last (n + 1))) (j : Fin (n + 4)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face R S j ≫ f = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face (mapNull f hf R) (mapNull f hf S) j := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face]
  split_ifs <;> try rfl
  rw [const_comp, hf]

/-- 差のホモトピー類は、基点を保つ射の誘導準同型で保たれる。 -/
theorem difference_map [KanComplex X] [KanComplex Y]
    (R S : PtSimplex.RelStruct .const s (Fin.last (n + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f hf (difference R S) =
      difference (mapNull f hf R) (mapNull f hf S) := by
  let φ := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible R S).liftOfKanComplex ≫ f
  have hφ (j : Fin (n + 4)) (hj : j ≠ (Fin.last (n + 1)).castSucc.castSucc) :
      stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face (mapNull f hf R) (mapNull f hf S) j := by
    rw [show φ = (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible R S).liftOfKanComplex ≫ f from rfl,
      ← Category.assoc, (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible R S).δ_liftOfKanComplex j hj, face_map]
  have h := difference_eq_ofFiller (mapNull f hf R) (mapNull f hf S) φ hφ
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f hf (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex R S)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk]
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex f hf (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex R S) =
      ofFiller (mapNull f hf R) (mapNull f hf S) φ hφ := by
    apply RelativeMorphism.ext
    rfl
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk hs).trans h.symm

end
end SerrePositivity.KST.Spectra.NullHomotopyDifference
