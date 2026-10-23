module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.Core.JoinTensor

/-!
概要：同じ底を固定した slice 関手の全族を、底と終点を固定した全余錐へ展開する。
方針：実相対評価と join・直積の比較を組み合わせる。
規約：固定条件は全次数の射の等式。使われ方：実補間の相対同型の uncurry。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X)
local notation "R" => relativeFunctorSpace (sliceOverProjection p) b

/-- 同じ底を固定した slice 関手の全相対評価を、パラメーターを左にして読む。 -/
def relativeSliceCoconeLeft : R ⊗ A ⟶ sliceOver p :=
  (β_ R A).hom ≫ relativeFunctorUncurry (𝟙 R)

/-- 相対評価は、全パラメーターで同じ元の底図式を保つ。 -/
lemma relativeSliceCoconeLeft_projection :
    relativeSliceCoconeLeft p b ≫ sliceOverProjection p = snd R A ≫ b := by
  rw [relativeSliceCoconeLeft, Category.assoc, relativeFunctorUncurry_projection]
  rfl

/-- 全相対 slice 関手を、元の形状と全パラメーター上の全余錐へ展開する普遍族。 -/
def relativeSliceCoconeUncurry : join A (Δ[0] : SSet.{u}) ⊗ R ⟶ X :=
  (β_ (join A Δ[0]) R).hom ≫ joinTensorLeft R A Δ[0] ≫
    sliceOverUncurry (relativeSliceCoconeLeft p b)

/-- 普遍全余錐の底は、元の同じ図式に全パラメーターで厳密に固定される。 -/
lemma relativeSliceCoconeUncurry_old :
    (joinInl A (Δ[0] : SSet.{u}) ▷ R) ≫ relativeSliceCoconeUncurry p b = fst A R ≫ b := by
  have hs : (joinInl A (Δ[0] : SSet.{u}) ▷ R) ≫ (β_ (join A Δ[0]) R).hom =
      (β_ A R).hom ≫ (R ◁ joinInl A Δ[0]) := by rfl
  rw [relativeSliceCoconeUncurry, ← Category.assoc, hs, Category.assoc,
    ← Category.assoc (R ◁ joinInl A Δ[0]), joinTensorLeft_inl,
    sliceOverUncurry_projection, relativeSliceCoconeLeft_projection,
    braiding_hom_snd_assoc]

/-- 普遍全余錐の頂点も、元の同じ指定点写像に全パラメーターで固定される。 -/
lemma relativeSliceCoconeUncurry_tip :
    (joinInr A (Δ[0] : SSet.{u}) ▷ R) ≫ relativeSliceCoconeUncurry p b = fst Δ[0] R ≫ p := by
  have hs : (joinInr A (Δ[0] : SSet.{u}) ▷ R) ≫ (β_ (join A Δ[0]) R).hom =
      (β_ Δ[0] R).hom ≫ (R ◁ joinInr A Δ[0]) := by rfl
  rw [relativeSliceCoconeUncurry, ← Category.assoc, hs, Category.assoc,
    ← Category.assoc (R ◁ joinInr A Δ[0]), joinTensorLeft_inr,
    Category.assoc, sliceOverUncurry_fixed, braiding_hom_snd_assoc]

end SerrePositivity.InfinityCategories.F2.Ind
