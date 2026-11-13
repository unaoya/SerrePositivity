module
public import SerrePositivity.KST.SConstruction.DGStandardEnrichedFunctor
public import SerrePositivity.KST.SConstruction.DGClosedWhiskerComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.EnrichedFunctors.AWClosedComposition

/-! # 全 Hom 閉零比較の標準 DK 豊穣自然変換
概要：元の全 Hom 上で自然な閉零射族を、標準 DK の豊穣自然変換へ移す。
方針：同じ閉零射の定数単体を使い、全成分の AW 前後合成を照合する。
規約：通常射だけの自然性や源の小ささを仮定しない。使われ方：Perf 作用の完全性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]

/-- 元の閉零射の全定数単体を束ねる標準 Hom への単位射。 -/
def dgStandardClosedMap {x y : E}
    (a : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := A) x y where
  app n := ↾fun _ => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv A E _ _ a) n.unop.len
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant_pullback (closedHomEquiv A E _ _ a) f.unop.toOrderHom).symm

variable (F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
  (a : ∀ x : D, ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (F.obj x) ⟶
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (G.obj x))
  (h : ∀ x y : D, F.map x y ≫
    eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex A) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (F.obj x)) (a y) =
    G.map x y ≫ eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex A) (a x)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (G.obj y)))

include h

/-- 全 Hom 自然性は、元の閉定数との AW 合成の全高次単体上の自然性を与える。 -/
lemma dgStandardClosedComparison_naturality {x y : D} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv A E _ _ (a y)) n)
        (dgStandardSimplexMap F s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (dgStandardSimplexMap G s)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv A E _ _ (a x)) n) := by
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData _ _).component J k hJ hk = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData _ _).component J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.awData_closed_post_component, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.awData_closed_pre_component]
  have he := congrArg (fun q => q.f k (s.val.component J k hJ hk)) (h x y)
  change (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex A) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (F.obj x))
      (a y)).f k ((F.map x y).f k (s.val.component J k hJ hk)) =
    (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex A) (a x)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (G.obj y))).f k
        ((G.map x y).f k (s.val.component J k hJ hk)) at he
  rw [dgClosedWhiskerLeft_f, dgClosedWhiskerRight_f] at he
  exact he

/-- 元の閉零比較は、標準 DK の全 Hom を保つ厳密な単体的豊穣自然変換。 -/
def dgStandardClosedComparison :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (dgStandardEnrichedFunctor F) (dgStandardEnrichedFunctor G) where
  app x := dgStandardClosedMap (a (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) x))
  naturality x y := by
    ext n s
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv A E _ _ (a (ForgetEnrichment.to (Complex A) y)))
          n.unop.len) (dgStandardSimplexMap F s.2) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (dgStandardSimplexMap G s.2)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv A E _ _ (a (ForgetEnrichment.to (Complex A) x)))
          n.unop.len)
    exact dgStandardClosedComparison_naturality F G a h s.2

end SerrePositivity.KST.SConstruction
