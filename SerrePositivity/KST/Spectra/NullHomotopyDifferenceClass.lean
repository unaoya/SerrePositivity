module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference
public import SerrePositivity.KST.Spectra.HornMissingFaceComparison

/-!
概要：二つの零ホモトピーの差の高次ホモトピー類と充填選択からの独立性。
方針：任意の充填の欠ける面を比較し、同じホーン上の相対ホモトピーを使う。
規約：零ホモトピーの代表そのものは固定し、Kan 充填だけの選択を消す。
使われ方：Goerss–Jardine VIII §1。lim¹ の差の族への幾何的な入力。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.NullHomotopyDifference

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌} {n : ℕ}
  {s : X.PtSimplex (n + 1) x}

/-- 任意の指定した差のホーンの充填から得る球面代表。 -/
def ofFiller (R S : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (φ : (Δ[n + 3] : SSet.{u}) ⟶ X)
    (hφ : ∀ j, j ≠ (Fin.last (n + 1)).castSucc.castSucc →
      stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face R S j) : X.PtSimplex (n + 2) x where
  map := stdSimplex.δ (Fin.last (n + 1)).castSucc.castSucc ≫ φ
  comm := by
    ext j : 1
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.output_face R S φ hφ j

/-- 二つの零ホモトピーの差の高次ホモトピー類。 -/
def difference (R S : PtSimplex.RelStruct .const s (Fin.last (n + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex R S)

/-- 任意の充填は、同じ差のホモトピー類を与える。 -/
lemma difference_eq_ofFiller (R S : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (φ : (Δ[n + 3] : SSet.{u}) ⟶ X)
    (hφ : ∀ j, j ≠ (Fin.last (n + 1)).castSucc.castSucc →
      stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face R S j) :
    difference R S = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (ofFiller R S φ hφ) := by
  apply missingFace_class_eq (Fin.last (n + 1)).castSucc.castSucc
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.simplex R S) (ofFiller R S φ hφ) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible R S).liftOfKanComplex φ rfl rfl
  apply horn.hom_ext
  intro j hj
  have he : horn.ι (Fin.last (n + 1)).castSucc.castSucc j hj ≫
      ((horn (n + 3) (Fin.last (n + 1)).castSucc.castSucc).ι ≫
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible R S).liftOfKanComplex) =
    horn.ι (Fin.last (n + 1)).castSucc.castSucc j hj ≫
      ((horn (n + 3) (Fin.last (n + 1)).castSucc.castSucc).ι ≫ φ) := by
    rw [horn.ι_ι_assoc, horn.ι_ι_assoc, (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.compatible R S).δ_liftOfKanComplex j hj, hφ j hj]
  have hv := congrArg SSet.yonedaEquiv he
  simpa only [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι] using hv

end
end SerrePositivity.KST.Spectra.NullHomotopyDifference
