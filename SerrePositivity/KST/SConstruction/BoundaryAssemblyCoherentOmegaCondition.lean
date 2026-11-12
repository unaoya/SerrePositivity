module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyCoherentComparison
public import SerrePositivity.KST.SConstruction.PointedKanDiagramComponentEquivalences

/-! # 元の構造射を保つ coherent な図式全体の Ω 条件
概要：境界模型の全体変換は元の構造射と基点固定でホモトピックで、図式全体の同型。
方針：元の任意の選択との成分一致から π_* 同型を移し、全体変換の可逆性を検出する。
規約：小さい通常の入力図式の全単体について述べる。スペクトル列の厳密化は別工程。
使われ方：元の BF K の Ω 条件を coherent な構造同型として回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の固定された随伴構造射と全体変換の回収成分は同じ点つき成分。 -/
lemma boundaryAssemblyCoherentDiagramMapAt_original_component {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    componentOf (boundaryKanAssemblyAdjoint r (F.obj i)) =
      componentOf (boundaryAssemblyCoherentDiagramMapAt r F i) := by
  obtain ⟨v⟩ := (boundaryKanAssemblyChoices_isContractibleKan r (F.obj i)).nonempty
  exact (boundaryKanAssemblyAdjointAt_component r (F.obj i) v).trans
    (boundaryAssemblyCoherentDiagramMapAt_component r F i v)

/-- 元の構造射を固定して、全体変換の回収成分への実際の基点固定ホモトピーを得る。 -/
lemma boundaryAssemblyCoherentDiagramMapAt_original_homotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    ∃ H : SSet.Homotopy (boundaryKanAssemblyAdjoint r (F.obj i)).right
        (boundaryAssemblyCoherentDiagramMapAt r F i).right,
      ((boundaryKanRealizationFunctor r).obj (F.obj i)).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          ((loopBoundaryKanFunctor (r + 1)).obj (F.obj i)).hom :=
  (piZero_eq_iff_pointedHomotopy _ _).mp (boundaryAssemblyCoherentDiagramMapAt_original_component r F i)

/-- 全体変換から回収した元の境界 Kan 模型間の成分は全基点 π_* 同型。 -/
lemma boundaryAssemblyCoherentDiagramMapAt_piIsomorphism {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (boundaryAssemblyCoherentDiagramMapAt r F i).right := by
  obtain ⟨H, _⟩ := boundaryAssemblyCoherentDiagramMapAt_original_homotopy r F i
  exact (kanPiIsomorphism_iff_of_homotopy H).mp (boundaryKanAssemblyAdjoint_piIsomorphism r (F.obj i))

/-- 元の構造射を回収する指定した全体変換は、図式全体での Ω 比較同型。 -/
def boundaryAssemblyCoherentDiagramIso {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor r)
        (fun i => boundaryKanRealization_kanComplex r (F.obj i)))
      (pointedKanCoherentDiagram (F ⋙ loopBoundaryKanFunctor (r + 1))
        (fun i => loopBoundaryKan_kanComplex (r + 1) (F.obj i))) :=
  pointedKanDiagramHomotopyFunctorIso
    (fun i => boundaryKanRealization_kanComplex r (F.obj i))
    (fun i => loopBoundaryKan_kanComplex (r + 1) (F.obj i))
    (boundaryAssemblyCoherentDiagramHomotopy r F) (boundaryAssemblyCoherentDiagramMapAt_piIsomorphism r F)

end SerrePositivity.KST.SConstruction
