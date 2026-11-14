module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGStrictNatTransSimplexWhisker

/-! # 厳密 dg 自然変換のホモトピー写像の前後合成

概要：二相単体の比較を、全 dg nerve の積上の写像の等式へ上げる。
方針：積の各単体に前後合成の単体等式を適用する。
規約：両端点だけでなく全時刻を保持。使われ方：実屋根 prism の商自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {B C D E : Type v}
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory A B] [_root_.SerrePositivity.DifferentialGraded.DGCategory A C] [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
variable {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor A C D}

/-- 自然変換の後合成は、その全ホモトピー写像の後合成に一致する。 -/
lemma dgStrictNatTransPostcomp_homotopyMap (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
    (Q : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η Q).homotopyMap = η.homotopyMap ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q := by
  ext n s
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp_simplex η Q s.1
    (SSet.stdSimplex.objEquiv s.2).toOrderHom

/-- 自然変換の前合成は、始域の全ホモトピー写像の引き戻しに一致する。 -/
lemma dgStrictNatTransPrecomp_homotopyMap (P : _root_.SerrePositivity.DifferentialGraded.DGFunctor A B C)
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp P η).homotopyMap =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P ▷ (Δ[1] : SSet.{max u v})) ≫ η.homotopyMap := by
  ext n s
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp_simplex P η s.1
    (SSet.stdSimplex.objEquiv s.2).toOrderHom

end SerrePositivity.InfinityCategories.Project.DerivedCategories
