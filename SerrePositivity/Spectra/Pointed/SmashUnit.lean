module

public import SerrePositivity.Spectra.Pointed.AdjoinBasepoint
public import SerrePositivity.Spectra.Pointed.SmashSymmetry
public import SerrePositivity.Spectra.Pointed.TensorCoproduct

/-!
# 零次球面による smash 積の単位

## 仮定と構成

閉直積モノイダル圏と有限余極限の下で、自由な基点を持つ零次球面が単位となる。
零次球面との直積は二つの成分からなり、第一成分を恒等、基点側の成分を定数として潰す。
直積の余積保存と smash の普遍性から、左単位同型を構成する。

## 注意

零次球面の非基点側の成分への包含は基点を保たない。
その包含を smash へ合成して初めて基点を保つことを確認して、逆射を定義する。
右単位同型は交換同型と左単位同型の合成で得る。
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
  [MonoidalClosed C] [HasFiniteColimits C]

/-- 零次球面との直積の非基点側の成分を選ぶ、基礎圏の射。 -/
def leftUnitSeed (X : PointedObject C) : X.right ⟶ (𝟙_ C ⨿ 𝟙_ C) ⊗ X.right :=
  (λ_ X.right).inv ≫ (coprod.inl ▷ X.right)

omit [MonoidalClosed C] in
/-- 零次球面との直積の基点側の成分は、第二の軸に等しい。 -/
lemma leftUnit_axisRight (X : PointedObject C) :
    (axisRight sphereZero X).right = (λ_ X.right).inv ≫ (coprod.inr ▷ X.right) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [axisRight, prodLift, sphereZero, adjoin]

omit [MonoidalClosed C] in
/-- 非基点側の成分の基点は、第一の軸上にある。 -/
lemma leftUnitSeed_basepoint (X : PointedObject C) :
    X.hom ≫ leftUnitSeed X = coprod.inl ≫ (axisLeft sphereZero X).right := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [leftUnitSeed, axisLeft, prodLift, sphereZero, adjoin, Category.assoc]

/-- 零次球面との直積で、非基点側を残し、基点側を定数にする射。 -/
def leftUnitRaw (X : PointedObject C) : (𝟙_ C ⨿ 𝟙_ C) ⊗ X.right ⟶ X.right :=
  tensorRightDesc (λ_ X.right).hom (toUnit (𝟙_ C ⊗ X.right) ≫ X.hom)

@[reassoc (attr := simp)] lemma leftUnitRaw_first (X : PointedObject C) :
    (coprod.inl ▷ X.right) ≫ leftUnitRaw X = (λ_ X.right).hom := tensorRightDesc_inl ..

@[reassoc (attr := simp)] lemma leftUnitRaw_second (X : PointedObject C) :
    (coprod.inr ▷ X.right) ≫ leftUnitRaw X = toUnit (𝟙_ C ⊗ X.right) ≫ X.hom :=
  tensorRightDesc_inr ..

@[reassoc (attr := simp)] lemma leftUnitSeed_raw (X : PointedObject C) :
    leftUnitSeed X ≫ leftUnitRaw X = 𝟙 X.right := by
  simp [leftUnitSeed, Category.assoc]

/-- 第二の軸上で、単位の候補射は基点で定数になる。 -/
lemma leftUnitRaw_axisRight (X : PointedObject C) :
    (axisRight sphereZero X).right ≫ leftUnitRaw X = toUnit X.right ≫ X.hom := by
  rw [leftUnit_axisRight]
  simp [Category.assoc]

/-- 第一の軸上でも、単位の候補射は基点で定数になる。
零次球面の二つの成分ごとに余積の普遍性を適用する。 -/
lemma leftUnitRaw_axisLeft (X : PointedObject C) :
    (axisLeft sphereZero X).right ≫ leftUnitRaw X =
      toUnit sphereZero.right ≫ X.hom := by
  apply coprod.hom_ext
  · rw [← Category.assoc, ← leftUnitSeed_basepoint, Category.assoc,
      leftUnitSeed_raw, Category.comp_id]
    simp [sphereZero, adjoin]
  · have h : (coprod.inr : 𝟙_ C ⟶ sphereZero.right) ≫
        (axisLeft sphereZero X).right =
        lift (𝟙 (𝟙_ C)) X.hom ≫ (coprod.inr ▷ X.right) := by
      apply CartesianMonoidalCategory.hom_ext <;>
        simp [axisLeft, prodLift, sphereZero, adjoin]
    rw [← Category.assoc, h, Category.assoc, leftUnitRaw_second]
    simp [sphereZero, adjoin]

/-- 基礎圏の単位の候補射は基点を保ち、基点付き直積からの射になる。 -/
def leftUnitProduct (X : PointedObject C) : prod sphereZero X ⟶ X :=
  Under.homMk (leftUnitRaw X) (by
    have h := leftUnitRaw_axisRight X
    have hpoint := Under.w (axisRight (sphereZero : PointedObject C) X)
    rw [← hpoint, Category.assoc, h]
    simp)

/-- 単位の候補射は、二つの軸を零にするので smash へ降りる。 -/
def leftUnitHom (X : PointedObject C) : smash sphereZero X ⟶ X :=
  smashDesc (leftUnitProduct X)
    (by
      apply Under.UnderMorphism.ext
      simpa only [Under.comp_right, zero_right, leftUnitProduct, Under.homMk_right] using
        leftUnitRaw_axisLeft X)
    (by
      apply Under.UnderMorphism.ext
      simpa only [Under.comp_right, zero_right, leftUnitProduct, Under.homMk_right] using
        leftUnitRaw_axisRight X)

@[reassoc (attr := simp)] lemma smashQuotient_leftUnitHom (X : PointedObject C) :
    smashQuotient sphereZero X ≫ leftUnitHom X = leftUnitProduct X := smashQuotient_desc ..

/-- 非基点側の包含を smash へ送ると基点を保つ。
元の基点は第一の軸上にあり、smash ではその軸が零となることを使う。 -/
def leftUnitInv (X : PointedObject C) : X ⟶ smash sphereZero X :=
  Under.homMk (leftUnitSeed X ≫ (smashQuotient sphereZero X).right) (by
    rw [← Category.assoc, leftUnitSeed_basepoint, Category.assoc]
    have h := congrArg Under.Hom.right (axisLeft_smashQuotient sphereZero X)
    rw [Under.comp_right] at h
    rw [h, zero_right]
    simp [sphereZero, adjoin])

/-- 左単位の逆射を単位射に合成すると恒等射になる。 -/
lemma leftUnitInv_hom (X : PointedObject C) : leftUnitInv X ≫ leftUnitHom X = 𝟙 X := by
  apply Under.UnderMorphism.ext
  change (leftUnitSeed X ≫ (smashQuotient sphereZero X).right) ≫ (leftUnitHom X).right = _
  rw [Category.assoc, ← Under.comp_right, smashQuotient_leftUnitHom]
  exact leftUnitSeed_raw X

/-- 単位射を逆射に合成すると smash 上の恒等射になる。
直積上へ引き戻し、零次球面の二つの成分で判定する。 -/
lemma leftUnitHom_inv (X : PointedObject C) :
    leftUnitHom X ≫ leftUnitInv X = 𝟙 (smash sphereZero X) := by
  apply smash_hom_ext
  simp only [smashQuotient_leftUnitHom_assoc, Category.comp_id]
  apply Under.UnderMorphism.ext
  change leftUnitRaw X ≫ (leftUnitSeed X ≫ (smashQuotient sphereZero X).right) = _
  apply tensorRightCoprod_hom_ext
  · simp [Category.assoc, leftUnitSeed, ← Category.assoc (λ_ X.right).hom]
  · rw [leftUnitRaw_second_assoc]
    have h := Under.w (leftUnitInv X)
    change X.hom ≫ (leftUnitSeed X ≫ (smashQuotient sphereZero X).right) = _ at h
    rw [h]
    have hq := congrArg Under.Hom.right (axisRight_smashQuotient sphereZero X)
    rw [Under.comp_right, leftUnit_axisRight] at hq
    have hi := congrArg (fun k ↦ (λ_ X.right).hom ≫ k) hq
    simpa [Category.assoc] using hi.symm

/-- 零次球面は smash 積の左単位となる。 -/
def smashLeftUnitor (X : PointedObject C) : smash sphereZero X ≅ X where
  hom := leftUnitHom X
  inv := leftUnitInv X
  hom_inv_id := leftUnitHom_inv X
  inv_hom_id := leftUnitInv_hom X

/-- 零次球面は smash 積の右単位となる。交換同型から得る。 -/
def smashRightUnitor (X : PointedObject C) : smash X sphereZero ≅ X :=
  smashSymmetry X sphereZero ≪≫ smashLeftUnitor X

/-- 単位の候補射は基点付き対象の射に関して自然。
直積の余積保存により、零次球面の二つの成分で確認する。 -/
lemma leftUnitRaw_naturality {X Y : PointedObject C} (f : X ⟶ Y) :
    sphereZero.right ◁ f.right ≫ leftUnitRaw Y = leftUnitRaw X ≫ f.right := by
  change (𝟙_ C ⨿ 𝟙_ C) ◁ f.right ≫ leftUnitRaw Y = leftUnitRaw X ≫ f.right
  apply tensorRightCoprod_hom_ext
  · rw [← whisker_exchange_assoc, leftUnitRaw_first, leftUnitRaw_first_assoc,
      leftUnitor_naturality]
  · rw [← whisker_exchange_assoc, leftUnitRaw_second, leftUnitRaw_second_assoc]
    simp

/-- smash の左単位同型は対象に関して自然。 -/
@[reassoc] lemma leftUnitHom_naturality {X Y : PointedObject C} (f : X ⟶ Y) :
    smashMap (𝟙 sphereZero) f ≫ leftUnitHom Y = leftUnitHom X ≫ f := by
  apply smash_hom_ext
  rw [smashQuotient_map_assoc, smashQuotient_leftUnitHom, smashQuotient_leftUnitHom_assoc]
  apply Under.UnderMorphism.ext
  simpa only [Under.comp_right, prodMap_right, Under.id_right, id_tensorHom,
    leftUnitProduct, Under.homMk_right] using leftUnitRaw_naturality f

/-- 左単位同型を関手の自然同型としてまとめる。 -/
def smashLeftUnitorNatIso :
    (smashFunctor (C := C)).obj sphereZero ≅ 𝟭 (PointedObject C) :=
  NatIso.ofComponents smashLeftUnitor (by
    intro X Y f
    exact leftUnitHom_naturality f)

/-- smash の右単位同型も対象に関して自然。 -/
@[reassoc] lemma rightUnitHom_naturality {X Y : PointedObject C} (f : X ⟶ Y) :
    smashMap f (𝟙 sphereZero) ≫ (smashRightUnitor Y).hom =
      (smashRightUnitor X).hom ≫ f := by
  change smashMap f (𝟙 sphereZero) ≫ (smashSwap Y sphereZero ≫ leftUnitHom Y) =
    (smashSwap X sphereZero ≫ leftUnitHom X) ≫ f
  rw [← Category.assoc, smashSwap_naturality, Category.assoc, leftUnitHom_naturality]
  simp [Category.assoc]

/-- 右単位同型を関手の自然同型としてまとめる。 -/
def smashRightUnitorNatIso :
    (smashFunctor (C := C)).flip.obj sphereZero ≅ 𝟭 (PointedObject C) :=
  NatIso.ofComponents smashRightUnitor (by
    intro X Y f
    exact rightUnitHom_naturality f)

end SerrePositivity.PointedObject
