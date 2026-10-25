module

public import SerrePositivity.InfinityCategories.F1B.Cones.ConeContraction
public import
  SerrePositivity.InfinityCategories.F1B.FunctorCategories.RetractionPrecompositionAdjunction

/-!
概要：余錐形状の右端への制限は、定値図式への前合成の左随伴。
方針：元の余錐の収縮を、切断と射影を固定する収縮の一般判定へ渡す。
規約：元の形状は任意。既存の深層ファイルを変更しない。
使われ方：全余錐族の相対普遍性を、その同じ右端へ反映する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 元の余錐形状を右端へ縮める、時間を第二因子とする実ホモトピー。 -/
def coconeShapeContraction (I : SSet.{u}) : SSet.Homotopy
    (𝟙 (join I (Δ[0] : SSet.{u})))
    (stdSimplex.isTerminalObj₀.from (join I Δ[0]) ≫ joinInr I Δ[0]) where
  h := (β_ (join I (Δ[0] : SSet.{u})) (Δ[1] : SSet.{u})).hom ≫ coneContraction I
  h₀ := by
    change prismEndpoint 0 (join I Δ[0]) ≫ coneContraction I = _
    exact coneContraction_zero I
  h₁ := by
    change prismEndpoint 1 (join I Δ[0]) ≫ coneContraction I = _
    rw [coneContraction_one]
    rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 余錐の収縮は右端を全時刻で固定する。 -/
lemma coconeShapeContraction_right (I : SSet.{u}) :
    (joinInr I (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (coconeShapeContraction I).h = fst Δ[0] Δ[1] ≫ joinInr I Δ[0] := by
  have h : (joinInr I (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (β_ (join I (Δ[0] : SSet.{u})) (Δ[1] : SSet.{u})).hom =
      (β_ (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ joinInr I Δ[0]) := by
    rfl
  change _ ≫ (_ ≫ coneContraction I) = _
  rw [← Category.assoc, h, Category.assoc, coneContraction,
    ← Category.assoc (Δ[1] ◁ joinInr I Δ[0]), joinTensorLeft_inr,
    Category.assoc, coneContractionCore_inr]
  rfl

/-- 余錐の右端への制限と、唯一の射影による前合成はホモトピー圏上で随伴。 -/
def coconeShapePrecompositionAdjunction (I X : SSet.{u}) :
    (hoFunctor.map ((pre (joinInr I (Δ[0] : SSet.{u}))).app X)).toFunctor ⊣
      (hoFunctor.map ((pre (stdSimplex.isTerminalObj₀.from (join I Δ[0]))).app X)).toFunctor :=
  retractionPrecompositionAdjunction _ _ (stdSimplex.isTerminalObj₀.hom_ext _ _)
    (coconeShapeContraction I) (coconeShapeContraction_right I)
    (stdSimplex.isTerminalObj₀.hom_ext _ _) X

end SerrePositivity.InfinityCategories.F1B
