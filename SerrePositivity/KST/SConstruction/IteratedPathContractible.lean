module
public import SerrePositivity.KST.SConstruction.IteratedPathFirstRow
public import SerrePositivity.KST.SConstruction.SPathRealization

/-! # 有限反復 S を施した経路実現の弱可縮性
概要：反復後も経路の全対角は弱可縮であり、第一行の反復実現も弱可縮となる。
方針：反復実現の関手を経路構成の後に合成し、一般の経路の収縮と零段の比較を使う。
規約：経路は最内側。使われ方：delooping の経路全空間の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：可縮 Kan な入力の全ての有限反復 S の各多次数も可縮 Kan。
方針：S_n が可縮 Kan 性を保つ既存の定理を方向数について帰納的に使う。
規約：安定な入力の圏の対象を使う。使われ方：反復後の零段の弱可縮性。 -/
lemma multiSConstruction_isContractibleKan_of_contractible (r : ℕ) (X : StableModel.{u})
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X.carrier) (d : Fin r → SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((multiSConstruction r X).obj d) := by
  induction r with
  | zero => exact hX
  | succ r ih =>
    rw [multiSConstruction_obj_succ]
    exact sConstruction_isContractibleKan_of_contractible _ (ih (fun i => d i.succ))

/-- 概要：可縮 Kan な入力の有限反復 S の core の各多次数も可縮 Kan。
方針：Kan な対象の core との同型で可縮性を移す。
規約：core を取る前の可縮性も証明済み。使われ方：対角実現の比較。 -/
lemma multiCoreSConstruction_isContractibleKan_of_contractible (r : ℕ) (X : StableModel.{u})
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X.carrier) (d : Fin r → SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((multiCoreSConstruction r X).obj d) := by
  have hc := multiSConstruction_isContractibleKan_of_contractible r X hX d
  let : KanComplex ((multiSConstruction r X).obj d) := hc.kanComplex
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso (kanCoreIso ((multiSConstruction r X).obj d)) hc

/-- 概要：可縮 Kan な入力の反復 core S の実現は弱可縮。
方針：対角添字上の各段から一点への自明ファイブレーションを対角の比較定理へ渡す。
規約：実現自体の Kan 性は不要。使われ方：経路の反復後の零段の比較。 -/
lemma multiRealization_toPoint_localized_isIso_of_contractible (r : ℕ) (X : StableModel.{u})
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X.carrier) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit ((multiRealizationFunctor r).obj X))) := by
  let M := multiIndexDiagonal r ⋙ multiCoreSConstruction r X
  let τ : M ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (𝟙_ SSet.{u}) := {
    app d := toUnit (M.obj d)
    naturality := by intros; exact isTerminalTensorUnit.hom_ext _ _ }
  have hi (d : SimplexCategoryᵒᵖ) : IsIso (AnodyneHomotopy.anodyneQ.map (τ.app d)) := by
    let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (τ.app d) := trivialKanFibration_toUnit_of_contractible
      (multiCoreSConstruction_isContractibleKan_of_contractible r X hX
        ((multiIndexDiagonal r).obj d))
    exact map_isIso_of_trivialKanFibration AnodyneHomotopy.anodyneQ
      (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions) (τ.app d)
  exact SerrePositivity.BisimplicialModel.localized_diagonal_map τ hi

/-- 概要：有限反復 S を施した経路の全対角実現は弱可縮。
方針：反復実現後も一般の経路構成であることを使い、零段の弱可縮性を組み合わせる。
規約：反復方向数零も含む。使われ方：反復の delooping の経路全空間。 -/
lemma iteratedPathRealization_toPoint_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (iteratedPathRealization r X))) := by
  let Q := AnodyneHomotopy.anodyneQ
  let P := simplicialStableEndofunctor ⋙ (evaluation StableModel.{u} StableModel.{u}).obj X ⋙
    multiRealizationFunctor r
  have hp := simplicialPathDiagonalProjection_image_isIso Q
    (Localization.inverts Q anodyneExtensions) P
  have hz : IsIso (Q.map (toUnit (P.obj (Opposite.op ⦋0⦌)))) :=
    multiRealization_toPoint_localized_isIso_of_contractible r (sStableModel 0 X)
      (sConstructionZero_isContractibleKan X.carrier)
  change IsIso (Q.map (toUnit (simplicialDiagonalFunctor.obj (simplicialPath P))))
  have he : simplicialPathDiagonalProjection P ≫ toUnit (P.obj (Opposite.op ⦋0⦌)) =
      toUnit (simplicialDiagonalFunctor.obj (simplicialPath P)) := isTerminalTensorUnit.hom_ext _ _
  rw [← he, Q.map_comp]
  infer_instance

/-- 概要：有限反復 S を施した第一行の全対角実現も弱可縮。
方針：経路との対角の弱同値と、経路全空間の弱可縮性を組み合わせる。
規約：homotopy fiber の計算は含めない。使われ方：第一行側の経路模型の比較。 -/
lemma iteratedFirstRowRealization_toPoint_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (iteratedFirstRowRealization r X))) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := iteratedPathFirstRowDiagonalComparison_localized_isIso r X
  have hc : IsIso (Q.map (iteratedPathFirstRowDiagonalComparison r X) ≫
      Q.map (toUnit (iteratedFirstRowRealization r X))) := by
    rw [← Q.map_comp, comp_toUnit]
    exact iteratedPathRealization_toPoint_localized_isIso r X
  exact (isIso_comp_left_iff _ _).mp hc

end SerrePositivity.KST.SConstruction
