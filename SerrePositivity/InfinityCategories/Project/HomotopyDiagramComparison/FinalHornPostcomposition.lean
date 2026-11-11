module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornFrontBoundary
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornLastPath

/-!
概要：最終外側ホーンの最終既知区間から、実際の後合成写像を回収する。
方針：隣接 Path の単位同型で射を抽出し、native 合成面の式を照合する。
規約：前半の未知 Hom は任意の写像として扱い、存在や境界可換性を仮定しない。
使われ方：HTT 5.2.4.6 の前半全境界と延長した後半 Hom の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open CategoryTheory.SimplicialThickening

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- 最後の既知区間 Hom の零単体から、元の最終区間の通常の射を回収する。 -/
def finalHornLastArrow : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2)) :=
  (eHomEquiv SSet).symm ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastPathIso n).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) (Fin.last (n + 2))
      (le_of_lt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))
      (Or.inl (ne_of_gt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n))))

/-- 回収した最終区間の射の豊穣像は、元の同じ既知区間 Hom の値に一致する。 -/
lemma finalHornLastArrow_eHom : eHomEquiv SSet (finalHornLastArrow σ) =
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornLastPathIso n).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) (Fin.last (n + 2))
        (le_of_lt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))
        (Or.inl (ne_of_gt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n))) :=
  (eHomEquiv SSet).apply_symm_apply _

/-- 前半 Path と合成面の同型は、元の最終区間の射による実際の後合成を与える。 -/
lemma finalHornFrontThroughIso_postcomposition
    (f : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontThroughIso n).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso (ULift.up.{u} (0 : Fin (n + 3)))
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) (ULift.up (Fin.last (n + 2)))).inv ≫
          (f ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalHom σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) (Fin.last (n + 2))
            (le_of_lt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))
            (Or.inl (ne_of_gt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n)))) ≫
              SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0)
                (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))) =
      f ≫ eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (finalHornLastArrow σ) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFrontThroughIso, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, Category.assoc, Iso.hom_inv_id_assoc]
  unfold eHomWhiskerLeft
  rw [finalHornLastArrow_eHom]
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro F
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
