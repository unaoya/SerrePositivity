module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementUnderEvaluation

/-!
概要：Under 重みの coend を、既存の同じ simplicial replacement の模型へ写す。
方針：既存の Under の普遍評価とその全自然性を、coend の dinaturality へ渡す。
規約：Kerodon Construction 5.3.2.1（Tag 035V）の既存模型の係数移送の法則。
使われ方：集合値係数での元の圏と native BK 余極限の比較への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {I : Type u} [SmallCategory I]

/-- 既存の Under の nerve からなる反変重み。 -/
abbrev underNerveWeight (I : Type u) [SmallCategory I] := Under.mapFunctor I ⋙ nerveFunctor

/-- 元の Under の普遍評価を、coend の指定した因子順序へ移す。 -/
def underWeightedColimitLeg (F : I ⥤ SSet.{u}) (i : I) :
    F.obj i ⊗ nerve (Under i) ⟶ simplicialReplacement F :=
  (β_ (F.obj i) (nerve (Under i))).hom ≫ simplicialReplacementUnderEvaluation F i

/-- 同じ普遍評価の自然性は coend の dinaturality そのもの。 -/
lemma underWeightedColimitLeg_condition (F : I ⥤ SSet.{u}) {i j : I} (f : i ⟶ j) :
    F.obj i ◁ (underNerveWeight I).map f.op ≫ underWeightedColimitLeg F i =
      F.map f ▷ nerve (Under j) ≫ underWeightedColimitLeg F j := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, τ⟩
  exact congrArg (fun g => g.app n (τ, x))
    (simplicialReplacementUnderEvaluation_naturality F f)

/-- Under 重みの既存 coend から同じ replacement への指定比較。 -/
def underWeightedColimitToReplacement (F : I ⥤ SSet.{u}) :
    weightedColimit (underNerveWeight I) F ⟶ simplicialReplacement F :=
  coend.desc (fun i => underWeightedColimitLeg F i) (fun _ _ f =>
    underWeightedColimitLeg_condition F f)

/-- 比較は各元の普遍脚で既存の Under の評価に一致する。 -/
lemma underWeightedColimitToReplacement_ι (F : I ⥤ SSet.{u}) (i : I) :
    weightedColimitι (underNerveWeight I) F i ≫ underWeightedColimitToReplacement F =
      underWeightedColimitLeg F i := by
  simp only [weightedColimitι, underWeightedColimitToReplacement, coend.ι_desc]

/-- 各脚での比較は、元の射列の底への忘却をそのまま保つ。 -/
lemma underWeightedColimitLeg_projection (F : I ⥤ SSet.{u}) (i : I) :
    underWeightedColimitLeg F i ≫ simplicialReplacementProjection F =
      snd (F.obj i) (nerve (Under i)) ≫ nerveMap (Under.forget i) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, τ⟩
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
