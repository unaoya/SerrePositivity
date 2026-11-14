module
public import SerrePositivity.EInfinity.HomotopyWeight.BousfieldKanCellTensor
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
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.DiagramModel SerrePositivity.DiagramModel.BousfieldKanCells
open SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

/-- 各自由BK細胞の終頂点における同じ非退化生成単体。 -/
def bkCellSimplex {n : ℕ} (c : (nerve I).nonDegenerate n) :
    (nerve (Over (c.val.obj (Fin.last n)))).nonDegenerate n :=
  (nondegenerateEquiv I n _).symm ⟨c, 𝟙 _⟩

/-- 元の重みの同じ骨格の塔。 -/
abbrev bkSkeleton := skeletonFiltration I (bousfieldKanWeight I)

/-- 全標準細胞から元の重みへの同じYoneda評価。 -/
def bkCellEvaluation (n : ℕ) : (bkCellTensor I n).obj Δ[n] ⟶ bousfieldKanWeight I :=
  bkCellDesc I Δ[n] (bousfieldKanWeight I)
    (fun c => yonedaEquiv.symm (bkCellSimplex I c).val)

/-- 元の自由細胞の境界から旧骨格への貼り付け写像。 -/
def bkCellBoundary (n : ℕ) : (bkCellTensor I n).obj (∂Δ[n] : SSet.{u}) ⟶
    (bkSkeleton I).obj n :=
  bkCellDesc I (∂Δ[n] : SSet.{u}) ((bkSkeleton I).obj n)
    (fun c => Subcomplex.lift
      (∂Δ[n].ι ≫ yonedaEquiv.symm (bkCellSimplex I c).val)
      (nondegenerate_boundary_range_skeleton (bkCellSimplex I c)))

/-- 元の自由細胞から新骨格への貼り付け写像。 -/
def bkCellTop (n : ℕ) : (bkCellTensor I n).obj Δ[n] ⟶ (bkSkeleton I).obj (n+1) :=
  bkCellDesc I Δ[n] ((bkSkeleton I).obj (n+1))
    (fun c => Subcomplex.lift (yonedaEquiv.symm (bkCellSimplex I c).val)
      (nondegenerate_range_skeleton (bkCellSimplex I c)))

/-- 元の新骨格の包含との合成は同じ細胞評価。 -/
theorem bkCellTop_ι (n : ℕ) :
    bkCellTop I n ≫ (skeletonCocone I (bousfieldKanWeight I)).ι.app (n+1) =
      bkCellEvaluation I n := by
  apply bkCellHom_ext I
  intro c
  change bkCellGenerator I c Δ[n] ≫ (bkCellTop I n).app _ ≫ _ = _
  dsimp only [bkCellTop, bkCellEvaluation]
  rw [← Category.assoc, bkCellGenerator_desc, bkCellGenerator_desc]
  rfl

/-- 二つの連続する元の骨格の間で、同じ自由境界の四角形は厳密に可換。 -/
theorem bkCellAttachment_comm (n : ℕ) :
    bkCellBoundary I n ≫ (bkSkeleton I).map (homOfLE (Nat.le_succ n)) =
      (bkCellTensor I n).map ∂Δ[n].ι ≫ bkCellTop I n := by
  apply bkCellHom_ext I
  intro c
  change bkCellGenerator I c (∂Δ[n] : SSet.{u}) ≫ (bkCellBoundary I n).app _ ≫ _ =
    bkCellGenerator I c (∂Δ[n] : SSet.{u}) ≫
      ((bkCellTensor I n).map ∂Δ[n].ι).app _ ≫ _
  dsimp only [bkCellBoundary, bkCellTop]
  rw [← Category.assoc, bkCellGenerator_desc, ← Category.assoc,
    bkCellGenerator_naturality, Category.assoc, bkCellGenerator_desc]
  apply (cancel_mono (((bousfieldKanWeight I).obj _).skeleton (n+1)).ι).mp
  rfl

end SerrePositivity.EInfinity.HomotopyWeight
