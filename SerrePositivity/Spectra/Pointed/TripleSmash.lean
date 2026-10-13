module

public import SerrePositivity.Spectra.Pointed.ProductColimits
public import SerrePositivity.Spectra.Pointed.ProductAssociator

/-!
# 三変数の reduced map と二段階の smash

三変数のどれかを基点にすると零になる射を、直積の三つの軸で記述する。
直積が pushout を保存することを使い、二つの変数を先に smash してから第三変数と smash する。
左右の括弧の両方について降下の普遍性とエピ性を構成する。
この段階の構成は結合子を前提とせず、その存在と整合性を証明するために使う。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [MonoidalClosed C] [HasFiniteColimits C]

/-- 左括弧の直積上で、三つの変数の基点を零にする射。 -/
abbrev TripleReducedMap (X Y Z W : PointedObject C) :=
  {f : prod (prod X Y) Z ⟶ W //
    prodMap (axisRight X Y) (𝟙 Z) ≫ f = 0 ∧
    prodMap (axisLeft X Y) (𝟙 Z) ≫ f = 0 ∧ axisLeft (prod X Y) Z ≫ f = 0}

/-- 右括弧の直積上で、同じ三つの基点を零にする射。 -/
abbrev RightTripleReducedMap (X Y Z W : PointedObject C) :=
  {f : prod X (prod Y Z) ⟶ W // axisRight X (prod Y Z) ≫ f = 0 ∧
    prodMap (𝟙 X) (axisRight Y Z) ≫ f = 0 ∧ prodMap (𝟙 X) (axisLeft Y Z) ≫ f = 0}

/-- 最初の二変数の smash の pushout は、第三変数との直積後も余極限である。 -/
abbrev leftSmashProductColimit (X Y Z : PointedObject C) :=
  isColimitOfHasPushoutOfPreservesColimit (prodRightFunctor Z)
    (wedgeToProd X Y) (toPoint (wedge X Y))

/-- 後ろの二変数の smash の pushout も、第一変数との直積後に余極限となる。 -/
abbrev rightSmashProductColimit (X Y Z : PointedObject C) :=
  isColimitOfHasPushoutOfPreservesColimit (prodLeftFunctor X)
    (wedgeToProd Y Z) (toPoint (wedge Y Z))

/-- 三変数で reduced な射を、最初の二変数の smash 後の直積へ降ろす。 -/
def leftSmashRawDesc {X Y Z W : PointedObject C} (f : TripleReducedMap X Y Z W) :
    prod (smash X Y) Z ⟶ W :=
  PushoutCocone.IsColimit.desc (leftSmashProductColimit X Y Z) f.1 0 (by
    dsimp only [prodRightFunctor]
    simp only [comp_zero]
    apply prodRightCoprod_hom_ext
    · simpa [← Category.assoc, wedgeToProd] using f.2.2.1
    · simpa [← Category.assoc, wedgeToProd] using f.2.1)

@[reassoc (attr := simp)] lemma leftSmashRawDesc_first {X Y Z W : PointedObject C}
    (f : TripleReducedMap X Y Z W) :
    prodMap (smashQuotient X Y) (𝟙 Z) ≫ leftSmashRawDesc f = f.1 :=
  PushoutCocone.IsColimit.inl_desc (leftSmashProductColimit X Y Z) f.1 0 _

@[reassoc (attr := simp)] lemma leftSmashRawDesc_second {X Y Z W : PointedObject C}
    (f : TripleReducedMap X Y Z W) :
    prodMap (pushout.inr (wedgeToProd X Y) (toPoint (wedge X Y))) (𝟙 Z) ≫
      leftSmashRawDesc f = 0 :=
      PushoutCocone.IsColimit.inr_desc (leftSmashProductColimit X Y Z) f.1 0 _

/-- 第三変数が基点のとき、最初の商へ降ろした射も零となる。 -/
lemma leftSmashRawDesc_axisLeft {X Y Z W : PointedObject C}
    (f : TripleReducedMap X Y Z W) : axisLeft (smash X Y) Z ≫ leftSmashRawDesc f = 0 := by
  apply (cancel_epi (smashQuotient X Y)).mp
  simp only [comp_zero]
  rw [← axisLeft_prodMap_assoc (smashQuotient X Y) (𝟙 Z) (leftSmashRawDesc f),
    leftSmashRawDesc_first]
  exact f.2.2.2

/-- 最初の二変数の smash が基点のときも、降ろした射は零となる。 -/
lemma leftSmashRawDesc_axisRight {X Y Z W : PointedObject C}
    (f : TripleReducedMap X Y Z W) : axisRight (smash X Y) Z ≫ leftSmashRawDesc f = 0 := by
  have h := congrArg (fun k ↦ axisRight (point : PointedObject C) Z ≫ k)
    (leftSmashRawDesc_second f)
  simpa only [axisRight_prodMap_assoc, Category.id_comp, comp_zero, smash] using h

/-- 三変数の射を、左括弧の二段階の smash へ降ろす。 -/
def leftTripleDesc {X Y Z W : PointedObject C} (f : TripleReducedMap X Y Z W) :
    smash (smash X Y) Z ⟶ W :=
  smashDesc (leftSmashRawDesc f) (leftSmashRawDesc_axisLeft f) (leftSmashRawDesc_axisRight f)

/-- 左括弧の二段階の smash への標準射。 -/
def leftTripleQuotient (X Y Z : PointedObject C) : prod (prod X Y) Z ⟶ smash (smash X Y) Z :=
  prodMap (smashQuotient X Y) (𝟙 Z) ≫ smashQuotient (smash X Y) Z

instance leftTripleQuotient_epi (X Y Z : PointedObject C) : Epi (leftTripleQuotient X Y Z) := by
  dsimp [leftTripleQuotient]
  infer_instance

@[reassoc (attr := simp)] lemma leftTripleQuotient_desc {X Y Z W : PointedObject C}
    (f : TripleReducedMap X Y Z W) : leftTripleQuotient X Y Z ≫ leftTripleDesc f = f.1 := by
  simp [leftTripleQuotient, leftTripleDesc, Category.assoc]

/-- 右括弧について、後ろの二変数を先に商へ降ろす。 -/
def rightSmashRawDesc {X Y Z W : PointedObject C} (f : RightTripleReducedMap X Y Z W) :
    prod X (smash Y Z) ⟶ W :=
  PushoutCocone.IsColimit.desc (rightSmashProductColimit X Y Z) f.1 0 (by
    dsimp only [prodLeftFunctor]
    simp only [comp_zero]
    apply prodLeftCoprod_hom_ext
    · simpa [← Category.assoc, wedgeToProd] using f.2.2.2
    · simpa [← Category.assoc, wedgeToProd] using f.2.2.1)

@[reassoc (attr := simp)] lemma rightSmashRawDesc_first {X Y Z W : PointedObject C}
    (f : RightTripleReducedMap X Y Z W) :
    prodMap (𝟙 X) (smashQuotient Y Z) ≫ rightSmashRawDesc f = f.1 :=
  PushoutCocone.IsColimit.inl_desc (rightSmashProductColimit X Y Z) f.1 0 _

@[reassoc (attr := simp)] lemma rightSmashRawDesc_second {X Y Z W : PointedObject C}
    (f : RightTripleReducedMap X Y Z W) :
    prodMap (𝟙 X) (pushout.inr (wedgeToProd Y Z) (toPoint (wedge Y Z))) ≫
      rightSmashRawDesc f = 0 :=
      PushoutCocone.IsColimit.inr_desc (rightSmashProductColimit X Y Z) f.1 0 _

/-- 右括弧の商へ降ろした射は、後ろの二変数の基点で零となる。 -/
lemma rightSmashRawDesc_axisLeft {X Y Z W : PointedObject C}
    (f : RightTripleReducedMap X Y Z W) : axisLeft X (smash Y Z) ≫ rightSmashRawDesc f = 0 := by
  have h := congrArg (fun k ↦ axisLeft X (point : PointedObject C) ≫ k)
    (rightSmashRawDesc_second f)
  simpa only [axisLeft_prodMap_assoc, Category.id_comp, comp_zero, smash] using h

/-- 右括弧の商へ降ろした射は、第一変数の基点でも零となる。 -/
lemma rightSmashRawDesc_axisRight {X Y Z W : PointedObject C}
    (f : RightTripleReducedMap X Y Z W) : axisRight X (smash Y Z) ≫ rightSmashRawDesc f = 0 := by
  apply (cancel_epi (smashQuotient Y Z)).mp
  simp only [comp_zero]
  rw [← axisRight_prodMap_assoc (𝟙 X) (smashQuotient Y Z) (rightSmashRawDesc f),
    rightSmashRawDesc_first]
  exact f.2.1

/-- 三変数の射を、右括弧の二段階の smash へ降ろす。 -/
def rightTripleDesc {X Y Z W : PointedObject C} (f : RightTripleReducedMap X Y Z W) :
    smash X (smash Y Z) ⟶ W :=
  smashDesc (rightSmashRawDesc f) (rightSmashRawDesc_axisLeft f) (rightSmashRawDesc_axisRight f)

/-- 右括弧の二段階の smash への標準射。 -/
def rightTripleQuotient (X Y Z : PointedObject C) : prod X (prod Y Z) ⟶ smash X (smash Y Z) :=
  prodMap (𝟙 X) (smashQuotient Y Z) ≫ smashQuotient X (smash Y Z)

instance rightTripleQuotient_epi (X Y Z : PointedObject C) : Epi (rightTripleQuotient X Y Z) := by
  dsimp [rightTripleQuotient]
  infer_instance

@[reassoc (attr := simp)] lemma rightTripleQuotient_desc {X Y Z W : PointedObject C}
    (f : RightTripleReducedMap X Y Z W) : rightTripleQuotient X Y Z ≫ rightTripleDesc f = f.1 := by
  simp [rightTripleQuotient, rightTripleDesc, Category.assoc]

/-- 左括弧の標準射は三変数で reduced。 -/
def leftTripleReduced (X Y Z : PointedObject C) :
    TripleReducedMap X Y Z (smash (smash X Y) Z) :=
  ⟨leftTripleQuotient X Y Z, by
    simp [leftTripleQuotient, ← Category.assoc, prodMap_zero_left] ; simp [Category.assoc], by
    simp [leftTripleQuotient, ← Category.assoc, prodMap_zero_left] ; simp [Category.assoc], by
    simp [leftTripleQuotient]⟩

/-- 右括弧の標準射も三変数で reduced。 -/
def rightTripleReduced (X Y Z : PointedObject C) :
    RightTripleReducedMap X Y Z (smash X (smash Y Z)) :=
  ⟨rightTripleQuotient X Y Z, by
    simp [rightTripleQuotient], by
    simp [rightTripleQuotient, ← Category.assoc, prodMap_zero_right] ; simp [Category.assoc], by
    simp [rightTripleQuotient, ← Category.assoc, prodMap_zero_right] ; simp [Category.assoc]⟩

/-- 左括弧の smash からの射は、三変数で reduced な射と同値。 -/
def leftTripleHomEquiv (X Y Z W : PointedObject C) :
    (smash (smash X Y) Z ⟶ W) ≃ TripleReducedMap X Y Z W where
  toFun f := ⟨leftTripleQuotient X Y Z ≫ f, by
    simpa only [leftTripleReduced, Category.assoc, zero_comp] using
      congrArg (fun k ↦ k ≫ f) (leftTripleReduced X Y Z).2.1, by
    simpa only [leftTripleReduced, Category.assoc, zero_comp] using
      congrArg (fun k ↦ k ≫ f) (leftTripleReduced X Y Z).2.2.1, by
    simpa only [leftTripleReduced, Category.assoc, zero_comp] using
      congrArg (fun k ↦ k ≫ f) (leftTripleReduced X Y Z).2.2.2⟩
  invFun := leftTripleDesc
  left_inv f := (cancel_epi (leftTripleQuotient X Y Z)).mp (leftTripleQuotient_desc _)
  right_inv f := Subtype.ext (leftTripleQuotient_desc f)

/-- 右括弧の smash からの射も、三変数で reduced な射と同値。 -/
def rightTripleHomEquiv (X Y Z W : PointedObject C) :
    (smash X (smash Y Z) ⟶ W) ≃ RightTripleReducedMap X Y Z W where
  toFun f := ⟨rightTripleQuotient X Y Z ≫ f, by
    simpa only [rightTripleReduced, Category.assoc, zero_comp] using
      congrArg (fun k ↦ k ≫ f) (rightTripleReduced X Y Z).2.1, by
    simpa only [rightTripleReduced, Category.assoc, zero_comp] using
      congrArg (fun k ↦ k ≫ f) (rightTripleReduced X Y Z).2.2.1, by
    simpa only [rightTripleReduced, Category.assoc, zero_comp] using
      congrArg (fun k ↦ k ≫ f) (rightTripleReduced X Y Z).2.2.2⟩
  invFun := rightTripleDesc
  left_inv f := (cancel_epi (rightTripleQuotient X Y Z)).mp (rightTripleQuotient_desc _)
  right_inv f := Subtype.ext (rightTripleQuotient_desc f)

end SerrePositivity.PointedObject
