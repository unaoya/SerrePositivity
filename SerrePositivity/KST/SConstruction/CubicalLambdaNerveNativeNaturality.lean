module
public import SerrePositivity.KST.SConstruction.CubicalLambdaNerveNativeIso
public import SerrePositivity.KST.SConstruction.CubicalLambdaNerveMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor

/-! # 元の実単体同型の厳密 dg 入力についての自然性
概要：Λ 実 dg 関手 nerve と native dg nerve の比較同型は、元の厳密 dg 後合成で自然。
方針：元の各単体での後合成等号を、元の単体的写像の全成分へ束ねる。
規約：元の全対象・Hom・全退化を保持。使われ方：native 直積と tensor source の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

/-- 元の実単体同型の順射は、元の厳密 dg 後合成と native dg nerve の写像を可換にする。 -/
lemma cubicalLambdaNerveNativeIso_naturality (F : DGFunctor A D E) :
    cubicalLambdaNerveMap A F ≫ (cubicalLambdaNerveNativeIso A E).hom =
      (cubicalLambdaNerveNativeIso A D).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
  ext n G
  exact cubicalLambdaNativeSimplex_post A G F

/-- 元の実単体同型の逆射も、元の厳密 dg 後合成と可換。 -/
lemma cubicalLambdaNerveNativeIso_inv_naturality (F : DGFunctor A D E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F ≫ (cubicalLambdaNerveNativeIso A E).inv =
      (cubicalLambdaNerveNativeIso A D).inv ≫ cubicalLambdaNerveMap A F := by
  ext n s
  exact simplexHAInverseFunctor_post A s F

end SerrePositivity.KST.SConstruction
