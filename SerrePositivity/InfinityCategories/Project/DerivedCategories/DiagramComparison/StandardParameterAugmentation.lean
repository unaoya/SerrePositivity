module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardSimplexParameter
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexContractionNaturality

/-!
概要：同じ自由正規化パラメータから、図式テンソル単位への増大写像を固定する。
方針：既存の正規化単体の自然な増大写像を、指定パラメータ同型で戻す。
規約：全単体作用素に自然で、各添字で同じ鎖写像を使う。
使われ方：HA 1.2.4、IS-W2 §73 A03、余作用の単位則の入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory
open _root_.SerrePositivity.ComplexLimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type v) [Category.{w} J]

/-- 元の標準単体の増大写像を、全パラメータの自由鎖図式へ戻す。 -/
def standardParameterAugmentation :
    liftedStandardSimplexParameter J ⋙ freeNegativeChainsDiagramFunctor A J ⟶
      𝟙_ (SimplexCategory ⥤ (J ⥤ CochainComplex (ModuleCat A) ℤ)) :=
  (freeStandardSimplexParameterIso A J).hom ≫ {
    app n := (Functor.const J).map (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom
    naturality := by
      intro n m f
      apply NatTrans.ext
      funext j
      change (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map
          (SSet.stdSimplex.map f) ≫ (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A m).hom =
        (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom ≫ 𝟙 _
      simpa only [Category.comp_id] using _root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction_naturality A f }

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
