module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveHornGenerators
public import SerrePositivity.HomotopicalAlgebra.Transfer.CellMap
public import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
概要：自由ホーンで生成された左射は、各値で元のanodyneな射。
方針：自由射の各値は同じホーンの余積で、余積・押し出し・逐次合成・レトラクトで移す。
規約：IS-W2 R03a.1の証明分割。モデル構造や弱同値のクラスを入力しない。
使われ方：元の比較射の自由ホーン分解の成分ごとの性質。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SSet
variable (K : Type u) [SmallCategory K]

/-- 元の自由ホーン射の各値は、同じホーン射の余積としてanodyne。 -/
theorem free_horn_anodyne (k l : K) {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.modelCategoryQuillen.J f) : SSet.anodyneExtensions (((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.free K k).map f).app l) := by
  have ha : SSet.modelCategoryQuillen.J.rlp.llp f := MorphismProperty.le_llp_rlp _ _ hf
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  intro A B p hp
  have freeHornLifting : ∀ _ : k ⟶ l, HasLiftingProperty f p := fun _ => ha _ hp
  letI := freeHornLifting
  change HasLiftingProperty (Limits.Sigma.map (fun _ : k ⟶ l => f)) p
  infer_instance

/-- 自由ホーン生成族を各値に評価すると、元のanodyne生成類に入る。 -/
theorem horns_evaluation_le (l : K) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.horns K ≤ SSet.anodyneExtensions.inverseImage (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.evaluation K l) := by
  intro A B f hf
  change (⨆ k, SSet.modelCategoryQuillen.J.strictMap (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.free K k)) f at hf
  rw [MorphismProperty.iSup_iff] at hf
  obtain ⟨k, hf⟩ := hf
  cases hf with
  | map hf => exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.free_horn_anodyne K k l _ hf

/-- 元のanodyneな射は、自由細胞の三つの閉包操作で保たれる。 -/
theorem anodyne_relativeCells_le :
    _root_.SerrePositivity.Quillen.relativeCells.{u} SSet.anodyneExtensions ≤ SSet.anodyneExtensions := by
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  exact (MorphismProperty.transfiniteCompositions_monotone
    ((MorphismProperty.pushouts_monotone SSet.modelCategoryQuillen.J.rlp.llp.coproducts_le).trans
      SSet.modelCategoryQuillen.J.rlp.llp.pushouts_le)).trans
        SSet.modelCategoryQuillen.J.rlp.llp.transfiniteCompositions_le

/-- 元の自由ホーンの全生成左類は、元の各値でanodyne。 -/
theorem projectiveHorn_anodyne {F G : K ⥤ SSet.{u}} (f : F ⟶ G)
    (hf : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.horns K).rlp.llp f) (l : K) : SSet.anodyneExtensions (f.app l) := by
  have evalColimits : PreservesColimitsOfSize.{u,u} (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.evaluation K l) :=
    { preservesColimitsOfShape := by intros; infer_instance }
  letI := evalColimits
  apply _root_.SerrePositivity.ModelGeneration.generatedLeft_le_of_cells_le (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.horns K)
    (SSet.anodyneExtensions.inverseImage (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.evaluation K l)) ?_ _ hf
  exact (_root_.SerrePositivity.ModelGeneration.relativeCells_map_le (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.evaluation K l) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.horns K)
    SSet.anodyneExtensions (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.horns_evaluation_le K l)).trans
      (fun _ _ _ h => _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.anodyne_relativeCells_le _ h)

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
