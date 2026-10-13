module

public import SerrePositivity.Spectra.Pointed.Smash

/-!
# 両変数で基点を潰す射

smash の二つの軸の零化条件を、基礎圏の直積の射について表す。
一方の変数を基点へ制限すると行き先の基点で定数になる射を、二変数の reduced map と呼ぶ。
この条件は写像の数学的性質であり、未証明入力を束ねる設定ではない。
smash の Hom と reduced map の同値を証明し、閉構造の curry へ渡せる形にする。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- 第二の軸の基礎圏での表示。第一変数を基点へ制限する射に対応する。 -/
lemma axisRight_right (X Y : PointedObject C) :
    (axisRight X Y).right = (λ_ Y.right).inv ≫ (X.hom ▷ Y.right) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [axisRight, prodLift]

/-- 第一の軸の基礎圏での表示。第二変数を基点へ制限する射に対応する。 -/
lemma axisLeft_right (X Y : PointedObject C) :
    (axisLeft X Y).right = (ρ_ X.right).inv ≫ (X.right ◁ Y.hom) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [axisLeft, prodLift]

/-- 第一変数を基点へ制限したときの定数性は、第二の軸上の定数性と同値。 -/
lemma reduced_left_iff {X Y Z : PointedObject C} (f : X.right ⊗ Y.right ⟶ Z.right) :
    (X.hom ▷ Y.right) ≫ f = toUnit (𝟙_ C ⊗ Y.right) ≫ Z.hom ↔
      (axisRight X Y).right ≫ f = toUnit Y.right ≫ Z.hom := by
  constructor
  · intro h
    rw [axisRight_right, Category.assoc, h]
    simp
  · intro h
    have h' := congrArg (fun k ↦ (λ_ Y.right).hom ≫ k) h
    simpa [axisRight_right, Category.assoc] using h'

/-- 第二変数を基点へ制限したときの定数性は、第一の軸上の定数性と同値。 -/
lemma reduced_right_iff {X Y Z : PointedObject C} (f : X.right ⊗ Y.right ⟶ Z.right) :
    (X.right ◁ Y.hom) ≫ f = toUnit (X.right ⊗ 𝟙_ C) ≫ Z.hom ↔
      (axisLeft X Y).right ≫ f = toUnit X.right ≫ Z.hom := by
  constructor
  · intro h
    rw [axisLeft_right, Category.assoc, h]
    simp
  · intro h
    have h' := congrArg (fun k ↦ (ρ_ X.right).hom ≫ k) h
    simpa [axisLeft_right, Category.assoc] using h'

/-- 一方の変数が基点なら、行き先の基点で定数となる二変数の射。 -/
abbrev ReducedPairMap (X Y Z : PointedObject C) :=
  {f : X.right ⊗ Y.right ⟶ Z.right //
    (X.hom ▷ Y.right) ≫ f = toUnit (𝟙_ C ⊗ Y.right) ≫ Z.hom ∧
    (X.right ◁ Y.hom) ≫ f = toUnit (X.right ⊗ 𝟙_ C) ≫ Z.hom}

/-- 両変数で reduced な射は、直積の基点を保つ。 -/
def reducedPairPointed {X Y Z : PointedObject C} (f : ReducedPairMap X Y Z) : prod X Y ⟶ Z :=
  Under.homMk f.1 (by
    rw [← Under.w (axisLeft X Y), Category.assoc, (reduced_right_iff f.1).mp f.2.2]
    simp)

@[simp] lemma reducedPairPointed_right {X Y Z : PointedObject C}
    (f : ReducedPairMap X Y Z) : (reducedPairPointed f).right = f.1 := rfl

/-- reduced な射は第一の軸を零にする。 -/
@[reassoc (attr := simp)] lemma reducedPairPointed_axisLeft {X Y Z : PointedObject C}
    (f : ReducedPairMap X Y Z) : axisLeft X Y ≫ reducedPairPointed f = 0 := by
  apply Under.UnderMorphism.ext
  simpa only [Under.comp_right, reducedPairPointed_right, zero_right] using
    (reduced_right_iff f.1).mp f.2.2

/-- reduced な射は第二の軸を零にする。 -/
@[reassoc (attr := simp)] lemma reducedPairPointed_axisRight {X Y Z : PointedObject C}
    (f : ReducedPairMap X Y Z) : axisRight X Y ≫ reducedPairPointed f = 0 := by
  apply Under.UnderMorphism.ext
  simpa only [Under.comp_right, reducedPairPointed_right, zero_right] using
    (reduced_left_iff f.1).mp f.2.1

variable [HasFiniteColimits C]

/-- smash からの射を、基礎圏の二変数の reduced map として取り出す。 -/
def smashToReduced {X Y Z : PointedObject C} (f : smash X Y ⟶ Z) : ReducedPairMap X Y Z :=
  ⟨(smashQuotient X Y).right ≫ f.right, by
    apply (reduced_left_iff _).mpr
    have h := congrArg Under.Hom.right
      (show axisRight X Y ≫ smashQuotient X Y ≫ f = 0 by simp)
    simpa only [Under.comp_right, zero_right, Category.assoc] using h, by
    apply (reduced_right_iff _).mpr
    have h := congrArg Under.Hom.right
      (show axisLeft X Y ≫ smashQuotient X Y ≫ f = 0 by simp)
    simpa only [Under.comp_right, zero_right, Category.assoc] using h⟩

/-- reduced map を、smash の普遍性で降ろす。 -/
def reducedToSmash {X Y Z : PointedObject C} (f : ReducedPairMap X Y Z) : smash X Y ⟶ Z :=
  smashDesc (reducedPairPointed f) (reducedPairPointed_axisLeft f) (reducedPairPointed_axisRight f)

/-- smash の Hom と、両変数で基点を潰す射の同値。 -/
def smashReducedHomEquiv (X Y Z : PointedObject C) :
    (smash X Y ⟶ Z) ≃ ReducedPairMap X Y Z where
  toFun := smashToReduced
  invFun := reducedToSmash
  left_inv f := by
    apply smash_hom_ext
    rw [show smashQuotient X Y ≫ reducedToSmash (smashToReduced f) =
        reducedPairPointed (smashToReduced f) from smashQuotient_desc ..]
    apply Under.UnderMorphism.ext
    rfl
  right_inv f := by
    apply Subtype.ext
    exact congrArg Under.Hom.right (smashQuotient_desc ..)

end SerrePositivity.PointedObject
