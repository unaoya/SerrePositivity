module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedNerveParameterFibration
public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionScaffoldValue

/-!
概要：under 切断の weighted nerve は、元の積上の left fibration として同じ scaffold を受け取る。
方針：係数射影を持つ一般の共同構成を適用し、taut 評価のパラメータを照合する。
規約：元の底と添字の両方を保つ。比較射の同値性は別に証明する。
使われ方：元の共同全空間と strict 分類図式との底上の比較 span。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B E : SSet.{u}} (p : E ⟶ B ⊗ nerve I)

/-- 元の切断族の係数射影は元の底への left fibration。 -/
instance underSectionTotalProjection_leftFibration [LeftFibration p] (i : I) :
    LeftFibration ((underSectionTotalProjection p).app i) :=
  underSectionFamilyProjection_leftFibration p i

/-- 元の under 切断図式の weighted nerve の、元の積への共同射影。 -/
def underSectionWeightedProjection :
    weightedNerve (underSectionTotalDiagram p) ⟶ B ⊗ nerve I :=
  weightedNerveParameterProjection (underSectionTotalProjection p)

instance underSectionWeightedProjection_leftFibration [LeftFibration p] :
    LeftFibration (underSectionWeightedProjection p) :=
  weightedNerveParameterProjection_leftFibration _

/-- 同じ taut scaffold は、元の係数のパラメータ射影を保つ。 -/
lemma underSectionTautScaffold_parameter :
    tautScaffold (underSectionTotalDiagram p) ≫
      weightedNerveParameter (underSectionTotalProjection p) = underSectionScaffoldBase p := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, τ⟩
  change _ = SSet.yonedaEquiv (τ ≫ (underSectionTotalProjection p).app (σ.obj 0))
  have h := congrArg SSet.yonedaEquiv
    (tautScaffold_parameter (underSectionTotalProjection p) ⟨σ, τ⟩)
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  rw [SSet.yonedaEquiv_comp]
  exact h

/-- 元の大域評価と同じ積上の射影を、同じ taut scaffold が持つ。 -/
lemma underSectionTautScaffold_over_product :
    tautScaffold (underSectionTotalDiagram p) ≫ underSectionWeightedProjection p =
      lift (underSectionScaffoldBase p)
        (simplicialReplacementProjection (underSectionTotalDiagram p)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, underSectionWeightedProjection, weightedNerveParameterProjection,
      lift_fst, underSectionTautScaffold_parameter, lift_fst]
  · rw [Category.assoc, underSectionWeightedProjection, weightedNerveParameterProjection,
      lift_snd, tautScaffold_projection, lift_snd]

end SerrePositivity.InfinityCategories.F2.Ind
