module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanCellAttachment
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanCellCoproduct

/-!
概要：自由細胞の各成分の貼り付け射を、元の非退化単体のYoneda写像に照合する。
方針：終頂点からの輸送の厳密な式と、同じYoneda写像の自然性を使う。
規約：IS-W2 R03aの同じ骨格押し出しの証明分割。
使われ方：既存の相対細胞の押し出しの四つの射との一致。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet
open _root_.SerrePositivity.DiagramModel.BousfieldKanCells
open _root_.SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped _root_.Simplicial
variable (I : Type u) [SmallCategory I]

/-- 同じ自由細胞の成分での降下射は、元の終頂点からの輸送。 -/
@[reassoc] theorem bkCellComponentInclusion_cellDesc {n : ℕ} {i : I}
    (s : NondegenerateData I n i) (X : SSet.{u}) (Z : I ⥤ SSet.{u})
    (f : ∀ c : (nerve I).nonDegenerate n, X ⟶ Z.obj (c.val.obj (Fin.last n))) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion I s X ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellDesc I X Z f).app i =
      f s.1 ≫ Z.map s.2 := rfl

/-- 同じ細胞の射は、すべての元の余積成分の包含を保つ。 -/
@[reassoc] theorem bkCellComponentInclusion_map {n : ℕ} {i : I}
    (s : NondegenerateData I n i) {X Y : SSet.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion I s X ≫ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).map f).app i =
      f ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion I s Y := rfl

/-- 終頂点での標準単体の輸送は、元の自由表示を逆に戻した単体そのもの。 -/
theorem bkCellSimplex_map {n : ℕ} {i : I} (s : NondegenerateData I n i) :
    ((bousfieldKanWeight I).map s.2).app (op ⦋n⦌) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellSimplex I s.1).val =
      ((nondegenerateEquiv I n i).symm s).val := by
  change overSimplex I ⟨s.1.val, 𝟙 _⟩ ⋙ Over.map s.2 = overSimplex I ⟨s.1.val, s.2⟩
  apply (simplexEquiv I n i).injective
  change simplexData I (overSimplex I ⟨s.1.val, 𝟙 _⟩ ⋙ Over.map s.2) =
    simplexData I (overSimplex I ⟨s.1.val, s.2⟩)
  rw [simplexData_postcomp, simplexData_overSimplex, simplexData_overSimplex]
  simp only [Category.id_comp]

/-- 各成分の細胞評価は、元の同じ非退化単体のYoneda写像。 -/
@[reassoc] theorem bkCellComponent_evaluation {n : ℕ} {i : I}
    (s : NondegenerateData I n i) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion I s Δ[n] ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellEvaluation I n).app i =
      yonedaEquiv.symm ((nondegenerateEquiv I n i).symm s).val := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellEvaluation, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion_cellDesc,
    yonedaEquiv_symm_comp, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellSimplex_map I s]
  rfl

/-- 各成分の新骨格への付着は、同じ標準単体の元の評価を保つ。 -/
@[reassoc] theorem bkCellComponent_top_ι {n : ℕ} {i : I}
    (s : NondegenerateData I n i) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion I s Δ[n] ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTop I n).app i ≫
      (((bousfieldKanWeight I).obj i).skeleton (n+1)).ι =
        yonedaEquiv.symm ((nondegenerateEquiv I n i).symm s).val := by
  have h := NatTrans.congr_app (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTop_ι I n) i
  change (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTop I n).app i ≫
    (((bousfieldKanWeight I).obj i).skeleton (n+1)).ι = (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellEvaluation I n).app i at h
  rw [h, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponent_evaluation]

/-- 各成分の旧骨格への付着は、元の標準境界の同じ評価を保つ。 -/
@[reassoc] theorem bkCellComponent_boundary_ι {n : ℕ} {i : I}
    (s : NondegenerateData I n i) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion I s (∂Δ[n] : SSet.{u}) ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellBoundary I n).app i ≫
      (((bousfieldKanWeight I).obj i).skeleton n).ι =
        ∂Δ[n].ι ≫ yonedaEquiv.symm ((nondegenerateEquiv I n i).symm s).val := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellBoundary, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion_cellDesc_assoc]
  change Subcomplex.lift _ _ ≫ skeletonMap ((bousfieldKanWeight I).map s.2) n ≫ _ = _
  rw [skeletonMap_ι, ← Category.assoc]
  change (∂Δ[n].ι ≫ yonedaEquiv.symm (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellSimplex I s.1).val) ≫
    (bousfieldKanWeight I).map s.2 = _
  rw [Category.assoc, yonedaEquiv_symm_comp]
  exact congrArg (fun z => ∂Δ[n].ι ≫ yonedaEquiv.symm z) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellSimplex_map I s)

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
