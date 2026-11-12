module
public import SerrePositivity.KST.SConstruction.StableMultiSCoreDiagram
public import SerrePositivity.KST.SConstruction.MultiSOneEnrichedComparison
public import SerrePositivity.KST.SConstruction.SimplicialEnrichedDiagramFunctor

/-!
概要：元の反復 S₁ 比較を、完全関手の core 全体に自然な比較にする。
方針：既存の全完全関手族の比較を core 包含で制限し、対象 core を取る。
規約：S₁ の段比較だけを扱う。BF スペクトルへの関手は構成しない。
使われ方：未完備 native 四角形の隣接正段比較で、同じ二胞体を保持する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet InfinityCategories LocalizingInvariants

/-- 概要：元の反復 core S₁ 比較は全自然同値族に厳密に自然。
方針：全完全関手族の既存比較を同じ core 包含へ制限する。
規約：比較の逆は選ばない。使われ方：有限 native 図式の全二胞体の比較。 -/
def stableMultiSOneCoreComparison (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison
      ((stableMultiSCoreEnrichedDiagram.{u} (r + 1)).obj
        ((oneDirectionIndex r).obj d))
      ((stableMultiSCoreEnrichedDiagram r).obj d) := by
  let P : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} ⥤
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} :=
    quasicategoryEnrichedPrecompositionFunctor (coreEnrichedInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
  let η := P.map (multiSOneQuasicategoryEnrichedComparison r d)
  exact quasicategoryEnrichedObjectCoreFunctor.map η

/-- 概要：同じ全族比較の成分は元の反復 core S₁ 比較。
方針：制限と対象 core の成分を展開する。
規約：同じ安定値を固定する。使われ方：元の S₁ 射の回収。 -/
lemma stableMultiSOneCoreComparison_val (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableMultiSOneCoreComparison r d).val C =
      (multiCoreSOneComparison r (stableCategoryModel C)).app d := rfl

/-- 概要：先頭 S 次数を一に固定した同じ全 core 図式。
方針：既存の全多次数図式を元の対角添字へ制限する。
規約：入力 Hom を離散化しない。使われ方：一次方向の実現作用。 -/
def stableOneDirectionCoreDiagram (r : ℕ) :
    SimplicialObject (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :=
  (multiIndexDiagonal r ⋙ oneDirectionIndex r) ⋙ stableMultiSCoreEnrichedDiagram (r + 1)

/-- 概要：一次方向の全 core 図式への厳密豊穣作用。
方針：既存の標準 end に全次数の作用を束ねる。
規約：実現と境界商は後続。使われ方：有限 native 図式上の S₁ 自然性。 -/
def stableOneDirectionObjectEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} SimplicialSSetDiagram.{u} :=
  simplicialEnrichedDiagramFunctor (stableOneDirectionCoreDiagram r)

/-- 概要：同じ作用の実値は元の一次方向 core 図式。
方針：元の対角と固定次数を展開する。
規約：対象の選び直しなし。使われ方：元の商構成との型照合。 -/
lemma stableOneDirectionObjectEnrichedFunctor_obj (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    ((stableOneDirectionObjectEnrichedFunctor r).obj C).diagram =
      multiIndexDiagonal r ⋙ oneDirectionIndex r ⋙
        multiCoreSConstruction (r + 1) (stableCategoryModel C) := rfl

end SerrePositivity.KST.SConstruction
