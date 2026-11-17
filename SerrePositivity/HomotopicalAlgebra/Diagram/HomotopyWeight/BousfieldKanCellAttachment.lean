module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanCellTensor
public import SerrePositivity.HomotopicalAlgebra.Diagram.SimplicialCellSkeleton
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan

/-!
概要：同じ自由BK細胞を、元の重みの二つの連続する骨格へ貼り付ける。
方針：終頂点の非退化単体のYoneda写像を自由生成元の降下射で束ねる。
規約：IS-W2 R03aの証明分割。骨格も単体も元のBK重みのもの。
使われ方：自由境界の押し出しによるBK重み全体の射影cofibrancy。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet
open _root_.SerrePositivity.DiagramModel _root_.SerrePositivity.DiagramModel.BousfieldKanCells
open _root_.SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped _root_.Simplicial
variable (I : Type u) [SmallCategory I]

/-- 各自由BK細胞の終頂点における同じ非退化生成単体。 -/
def bkCellSimplex {n : ℕ} (c : (nerve I).nonDegenerate n) :
    (nerve (Over (c.val.obj (Fin.last n)))).nonDegenerate n :=
  (nondegenerateEquiv I n _).symm ⟨c, 𝟙 _⟩

/-- 元の重みの同じ骨格の塔。 -/
abbrev bkSkeleton := skeletonFiltration I (bousfieldKanWeight I)

/-- 全標準細胞から元の重みへの同じYoneda評価。 -/
def bkCellEvaluation (n : ℕ) : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).obj Δ[n] ⟶ bousfieldKanWeight I :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellDesc I Δ[n] (bousfieldKanWeight I)
    (fun c => yonedaEquiv.symm (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellSimplex I c).val)

/-- 元の自由細胞の境界から旧骨格への貼り付け写像。 -/
def bkCellBoundary (n : ℕ) : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).obj (∂Δ[n] : SSet.{u}) ⟶
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeleton I).obj n :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellDesc I (∂Δ[n] : SSet.{u}) ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeleton I).obj n)
    (fun c => Subcomplex.lift
      (∂Δ[n].ι ≫ yonedaEquiv.symm (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellSimplex I c).val)
      (nondegenerate_boundary_range_skeleton (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellSimplex I c)))

/-- 元の自由細胞から新骨格への貼り付け写像。 -/
def bkCellTop (n : ℕ) : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).obj Δ[n] ⟶ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeleton I).obj (n+1) :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellDesc I Δ[n] ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeleton I).obj (n+1))
    (fun c => Subcomplex.lift (yonedaEquiv.symm (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellSimplex I c).val)
      (nondegenerate_range_skeleton (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellSimplex I c)))

/-- 元の新骨格の包含との合成は同じ細胞評価。 -/
theorem bkCellTop_ι (n : ℕ) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTop I n ≫ (skeletonCocone I (bousfieldKanWeight I)).ι.app (n+1) =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellEvaluation I n := by
  apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellHom_ext I
  intro c
  change _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellGenerator I c Δ[n] ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTop I n).app _ ≫ _ = _
  dsimp only [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTop, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellEvaluation]
  rw [← Category.assoc, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellGenerator_desc, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellGenerator_desc]
  rfl

/-- 二つの連続する元の骨格の間で、同じ自由境界の四角形は厳密に可換。 -/
theorem bkCellAttachment_comm (n : ℕ) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellBoundary I n ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeleton I).map (homOfLE (Nat.le_succ n)) =
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).map ∂Δ[n].ι ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTop I n := by
  apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellHom_ext I
  intro c
  change _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellGenerator I c (∂Δ[n] : SSet.{u}) ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellBoundary I n).app _ ≫ _ =
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellGenerator I c (∂Δ[n] : SSet.{u}) ≫
      ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).map ∂Δ[n].ι).app _ ≫ _
  dsimp only [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellBoundary, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTop]
  rw [← Category.assoc, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellGenerator_desc, ← Category.assoc,
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellGenerator_naturality, Category.assoc, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellGenerator_desc]
  apply (cancel_mono (((bousfieldKanWeight I).obj _).skeleton (n+1)).ι).mp
  rfl

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
