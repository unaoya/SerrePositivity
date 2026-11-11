module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleRelativeComparison
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation

/-!
概要：元の相対三角形比較は、同じ全族の比較の元の一点成分の表示変更である。
方針：元の相対比較を定義する両端の頂点表示の等式輸送を除く。
規約：元の二単体と指定値を保持。使われ方：下面の区間族比較との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c)

/-- 元の相対比較の値は、同じ全三角形比較の一点成分の値に一致する。 -/
lemma functorTriangleRelativeComparison_heq_family_app :
    HEq (functorTriangleRelativeComparison T)
      ((unstraighteningMappingTriangleIso F G J
        (SSet.const (coherentVertexOfHomotopy a)) (SSet.const (coherentVertexOfHomotopy b))
        (SSet.const (coherentVertexOfHomotopy c))
        (coherentTriangleOfFunctorTriangle T).diagram (coherentTriangleOfFunctorTriangle T).first
        (coherentTriangleOfFunctorTriangle T).second (coherentTriangleOfFunctorTriangle T).long).app
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) := by
  unfold functorTriangleRelativeComparison unstraighteningTriangleRelativeVertexIso
  exact iso_endpoints_heq _ _ _

end SerrePositivity.InfinityCategories.F2
