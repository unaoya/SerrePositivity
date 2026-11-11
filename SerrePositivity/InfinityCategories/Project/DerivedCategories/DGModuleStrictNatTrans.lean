module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations

/-! # 全 Hom 自然な閉加群射族の厳密 dg 自然変換

概要：主 Hom 複体上の前後合成の等式を厳密 dg 自然性へ変換する。
方針：全次数の斉次元で評価し、主 Hom end の評価により合成と照合する。
規約：次数零の通常自然性では代用しない。使われ方：延長と Yoneda の実関手比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]

/-- 主 Hom の閉射による後合成は、閉零 cycle との全次数の合成。 -/
lemma dgModuleHomPostcompose_apply {M N P : _root_.SerrePositivity.DifferentialGraded.RightModule A E}
    (a : ForgetEnrichment.of (Complex A) N ⟶ ForgetEnrichment.of (Complex A) P)
    {k : ℤ} (z : _root_.SerrePositivity.DifferentialGraded.GradedHom A M N k) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose A E M N P a).f k z =
      _root_.SerrePositivity.DifferentialGraded.compose A (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) a)).val z
        (add_zero k) := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext A E
  intro e
  rw [_root_.SerrePositivity.DifferentialGraded.moduleHomCompose_π]
  erw [← moduleEvaluation_cochain A E e a]
  exact moduleHomWhiskerLeft_apply_π A E a k z e

/-- 主 Hom の閉射による前合成は、閉零 cycle との全次数の合成。 -/
lemma dgModuleHomPrecompose_apply {M N P : _root_.SerrePositivity.DifferentialGraded.RightModule A E}
    (a : ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) N)
    {k : ℤ} (z : _root_.SerrePositivity.DifferentialGraded.GradedHom A N P k) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHomPrecompose A E M N P a).f k z =
      _root_.SerrePositivity.DifferentialGraded.compose A z (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) a)).val
        (zero_add k) := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext A E
  intro e
  rw [_root_.SerrePositivity.DifferentialGraded.moduleHomCompose_π]
  erw [← moduleEvaluation_cochain A E e a]
  exact moduleHomWhiskerRight_apply_π A E a k z e

variable {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D (RightModule A E)}

/-- 全 Hom 複体に関して自然な閉零加群射族を厳密 dg 自然変換へ束ねる。 -/
def dgModuleStrictNatTransOfHomNaturality
    (a : ∀ x, ForgetEnrichment.of (Complex A) (F.obj x) ⟶
      ForgetEnrichment.of (Complex A) (G.obj x))
    (h : ∀ x y, F.map x y ≫ _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose A E _ _ _ (a y) =
      G.map x y ≫ _root_.SerrePositivity.DifferentialGraded.moduleHomPrecompose A E _ _ _ (a x)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G where
  app x := _root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a x))
  naturality {x y k} f := by
    have he := congrArg (fun q => q.f k f) (h x y)
    change (moduleHomPostcompose A E _ _ _ (a y)).f k ((F.map x y).f k f) =
      (moduleHomPrecompose A E _ _ _ (a x)).f k ((G.map x y).f k f) at he
    rw [dgModuleHomPostcompose_apply, dgModuleHomPrecompose_apply] at he
    exact he

end SerrePositivity.InfinityCategories.Project.DerivedCategories
