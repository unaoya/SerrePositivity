module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LiftedStandardSimplexParameterEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedSimplexInverseAdjunction

/-!
概要：元の実標準Hom単体のDK像の逆正規化Hom同値を全生成元で評価する。
方針：同じYonedaパラメータの評価則と指定逆随伴の生成元評価を使う。
規約：元の全標準単体パラメータとDK同型を保持する既存構成の法則。
使われ方：HA 1.2.4、IS-W2 B02のAW各切断の第二因子。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の実標準Hom単体のDK像の逆射は、指定Yonedaパラメータの同じ最上位成分を返す。 -/
theorem normalizedSimplexHomEquiv_native_generator (x y : D) (m : SimplexCategory)
    (α : (standardHomSpace (R := A) x y).obj (Opposite.op m)) (n : ℕ)
    (s : ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)).obj
      (Opposite.op ⦋n⦌)) :
    ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A (homObject A D x y) m).symm
      ((standardDoldKanSpaceMap x y).app (Opposite.op m) α)).f (-(n : ℤ))
        (freeNegativeGenerator
          ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) n s) =
      standardTopEval (R := A) x y n
        (((liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm α).app
          (Opposite.op ⦋n⦌)) s) := by
  let f := liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm α
  have h := normalizedSimplexHomEquiv_symm_standard_generator A x y m f n s
  have he := liftedStandardSimplexHomIso_yoneda_postcomp (standardDoldKanSpaceMap x y) m α
  have h' := congrArg (fun t => ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A (homObject A D x y) m).symm t).f
    (-(n : ℤ)) (freeNegativeGenerator
      ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) n s)) he
  exact h'.symm.trans h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
