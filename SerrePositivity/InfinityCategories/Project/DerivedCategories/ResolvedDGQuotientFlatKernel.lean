module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientVerdierSequence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ResolvedDGQuotientStability
/-!
概要：同じ cell 平坦分解の中に実小 dg 核を取り、同じ平坦商への Verdier 列を公開する。
方針：指定対象の逆像の実安定閉包を充満 dg 部分圏とし、既存の商普遍性へ接続する。
規約：元の圏から商への厳密 dg 射を追加せず、同じ平坦源と同じ商を保持する。
使われ方：D-9、非連結懸垂の平坦屋根と Sp 側の相対 Verdier 四角形への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 同じ平坦源の中に取る、指定対象の逆像の実安定閉包。 -/
abbrev resolvedDGQuotientFlatKernel (P : Set D) :=
  _root_.SerrePositivity.DifferentialGraded.DGFullSubcategory (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source A D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty A (DGCategoryCellResolution.Source A D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects A D P))

/-- 核の対象型も係数環と同じ宇宙で小さい。 -/
lemma resolvedDGQuotientFlatKernel_small (P : Set D) :
    Small.{u} (resolvedDGQuotientFlatKernel A D P) := inferInstance

/-- 核の Hom 複体も同じ平坦源の Hom なので K-flat。 -/
lemma resolvedDGQuotientFlatKernel_homKFlat (P : Set D) :
    _root_.SerrePositivity.DifferentialGraded.localHomKFlat A (resolvedDGQuotientFlatKernel A D P) :=
  fun x y => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.source_homKFlat A D x.val y.val

/-- 右辺は同じ指定対象の逆像を零化する厳密 dg 商包含の nerve。 -/
lemma resolvedDGQuotientProjection_eq_nerve (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection A D P =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGQuotient.inclusion A (DGCategoryCellResolution.Source A D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects A D P)) := rfl

/-- 同じ平坦源への実際の厳密 dg 包含。 -/
def resolvedDGQuotientFlatKernelInclusion (P : Set D) :
    _root_.SerrePositivity.DifferentialGraded.DGFunctor A (resolvedDGQuotientFlatKernel A D P) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source A D) :=
  _root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion A _ _

/-- この包含の nerve は既存の安定閉包の包含そのもの。 -/
lemma resolvedDGQuotientFlatKernelInclusion_nerve (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (resolvedDGQuotientFlatKernelInclusion A D P) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion A (DGCategoryCellResolution.Source A D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects A D P) := rfl

/-- 核の nerve は実際に安定である。 -/
lemma resolvedDGQuotientFlatKernel_isStable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (resolvedDGQuotientFlatKernel A D P)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated A D
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureNerve_isStable A _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects A D P)

/-- 同じ平坦源からの商射影と実小核の包含は Verdier 列をなす。 -/
theorem resolvedDGQuotientFlatKernel_isStableVerdierSequence
    [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] (P : Set D) :
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated A D
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated A (DGCategoryCellResolution.Source A D)
    let := resolvedDGQuotientFlatKernel_isStable A D P
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve_isStable A D P
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsStableVerdierSequence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (resolvedDGQuotientFlatKernelInclusion A D P))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection A D P) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated A D
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotient_isStableVerdierSequence A _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects A D P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat A D P)

/-- 元の圏からの同じ屋根は、分解上で同じ商射影に可逆二胞体で一致する。 -/
def resolvedDGQuotientFlatKernel_roof (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation A D) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor A D P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection A D P) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientRoofIso A D P

end SerrePositivity.InfinityCategories.Project.DerivedCategories
