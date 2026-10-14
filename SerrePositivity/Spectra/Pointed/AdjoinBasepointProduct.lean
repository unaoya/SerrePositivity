module

public import SerrePositivity.Spectra.Pointed.AdjoinBasepoint
public import SerrePositivity.Spectra.Pointed.Smash
public import SerrePositivity.Spectra.Pointed.TensorCoproduct

/-!
# 自由な基点の追加と直積

閉直積モノイダル圏で、二つの自由基点付き対象の smash は、
元の直積に自由な基点を追加した対象と同型になる。
余積の四成分のうち基点を含む三成分を潰し、残りの成分を保持する。
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

/-- 四成分のうち、元の直積だけを保持する基礎圏の射。 -/
def adjoinProductRaw (X Y : C) : (X ⨿ 𝟙_ C) ⊗ (Y ⨿ 𝟙_ C) ⟶ (X ⊗ Y) ⨿ 𝟙_ C :=
  tensorCoprodDesc coprod.inl (toUnit _ ≫ coprod.inr)
    (toUnit _ ≫ coprod.inr) (toUnit _ ≫ coprod.inr)

@[reassoc (attr := simp)] lemma adjoinProductRaw_first (X Y : C) :
    (coprod.inl ⊗ₘ coprod.inl) ≫ adjoinProductRaw X Y = coprod.inl := by
  simp [adjoinProductRaw]

/-- 第一因子の基点成分は定数になる。 -/
@[reassoc (attr := simp)] lemma adjoinProductRaw_basepoint_left (X Y : C) :
    (coprod.inr ▷ (Y ⨿ 𝟙_ C)) ≫ adjoinProductRaw X Y =
      toUnit (𝟙_ C ⊗ (Y ⨿ 𝟙_ C)) ≫ coprod.inr := by
  apply tensorLeftCoprod_hom_ext
  · rw [← Category.assoc, ← tensorHom_def']
    simp [adjoinProductRaw]
  · rw [← Category.assoc, ← tensorHom_def']
    simp [adjoinProductRaw]

/-- 第二因子の基点成分も定数になる。 -/
@[reassoc (attr := simp)] lemma adjoinProductRaw_basepoint_right (X Y : C) :
    ((X ⨿ 𝟙_ C) ◁ coprod.inr) ≫ adjoinProductRaw X Y =
      toUnit ((X ⨿ 𝟙_ C) ⊗ 𝟙_ C) ≫ coprod.inr := by
  apply tensorRightCoprod_hom_ext
  · rw [← Category.assoc, ← tensorHom_def]
    simp [adjoinProductRaw]
  · rw [← Category.assoc, ← tensorHom_def]
    simp [adjoinProductRaw]

omit [MonoidalClosed C] in
/-- 第一軸は第二因子の基点成分を経由する。 -/
lemma adjoin_axisLeft (X Y : C) :
    (axisLeft (adjoin X) (adjoin Y)).right =
      (ρ_ (X ⨿ 𝟙_ C)).inv ≫ ((X ⨿ 𝟙_ C) ◁ coprod.inr) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [axisLeft, prodLift, adjoin]

omit [MonoidalClosed C] in
/-- 第二軸は第一因子の基点成分を経由する。 -/
lemma adjoin_axisRight (X Y : C) :
    (axisRight (adjoin X) (adjoin Y)).right =
      (λ_ (Y ⨿ 𝟙_ C)).inv ≫ (coprod.inr ▷ (Y ⨿ 𝟙_ C)) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [axisRight, prodLift, adjoin]

/-- 基礎圏の比較は第一軸を基点へ送る。 -/
lemma adjoinProductRaw_axisLeft (X Y : C) :
    (axisLeft (adjoin X) (adjoin Y)).right ≫ adjoinProductRaw X Y =
      toUnit (adjoin X).right ≫ (adjoin (X ⊗ Y)).hom := by
  rw [adjoin_axisLeft]
  simp [Category.assoc, adjoin]

/-- 基礎圏の比較は第二軸も基点へ送る。 -/
lemma adjoinProductRaw_axisRight (X Y : C) :
    (axisRight (adjoin X) (adjoin Y)).right ≫ adjoinProductRaw X Y =
      toUnit (adjoin Y).right ≫ (adjoin (X ⊗ Y)).hom := by
  rw [adjoin_axisRight]
  simp [Category.assoc, adjoin]

/-- 四成分の比較を基点付き直積の射にする。 -/
def adjoinProductMap (X Y : C) : prod (adjoin X) (adjoin Y) ⟶ adjoin (X ⊗ Y) :=
  Under.homMk (adjoinProductRaw X Y) (by
    rw [← Under.w (axisRight (adjoin X) (adjoin Y)), Category.assoc,
      adjoinProductRaw_axisRight]
    simp)

/-- 両軸の零化から、自由基点付き対象の smash の比較射を得る。 -/
def adjoinSmashHom (X Y : C) : smash (adjoin X) (adjoin Y) ⟶ adjoin (X ⊗ Y) :=
  smashDesc (adjoinProductMap X Y)
    (by
      apply Under.UnderMorphism.ext
      simpa only [Under.comp_right, zero_right, adjoinProductMap, Under.homMk_right] using
        adjoinProductRaw_axisLeft X Y)
    (by
      apply Under.UnderMorphism.ext
      simpa only [Under.comp_right, zero_right, adjoinProductMap, Under.homMk_right] using
        adjoinProductRaw_axisRight X Y)

@[reassoc (attr := simp)] lemma smashQuotient_adjoinSmashHom (X Y : C) :
    smashQuotient (adjoin X) (adjoin Y) ≫ adjoinSmashHom X Y = adjoinProductMap X Y :=
  smashQuotient_desc ..

/-- 元の直積を非基点成分として smash へ入れる射。 -/
def adjoinSmashInv (X Y : C) : adjoin (X ⊗ Y) ⟶ smash (adjoin X) (adjoin Y) :=
  (adjoinHomEquiv _ _).symm
    ((coprod.inl ⊗ₘ coprod.inl) ≫ (smashQuotient (adjoin X) (adjoin Y)).right)

omit [MonoidalClosed C] in
/-- smash の商写像は第二因子の基点成分を潰す。 -/
@[reassoc (attr := simp)] lemma adjoinQuotient_basepoint_right (X Y : C) :
    ((X ⨿ 𝟙_ C) ◁ coprod.inr) ≫ (smashQuotient (adjoin X) (adjoin Y)).right =
      toUnit ((X ⨿ 𝟙_ C) ⊗ 𝟙_ C) ≫ (smash (adjoin X) (adjoin Y)).hom := by
  have h := congrArg Under.Hom.right (axisLeft_smashQuotient (adjoin X) (adjoin Y))
  rw [Under.comp_right, adjoin_axisLeft, zero_right] at h
  have h' := congrArg (fun f ↦ (ρ_ (X ⨿ 𝟙_ C)).hom ≫ f) h
  simpa [adjoin, Category.assoc] using h'

omit [MonoidalClosed C] in
/-- smash の商写像は第一因子の基点成分を潰す。 -/
@[reassoc (attr := simp)] lemma adjoinQuotient_basepoint_left (X Y : C) :
    (coprod.inr ▷ (Y ⨿ 𝟙_ C)) ≫ (smashQuotient (adjoin X) (adjoin Y)).right =
      toUnit (𝟙_ C ⊗ (Y ⨿ 𝟙_ C)) ≫ (smash (adjoin X) (adjoin Y)).hom := by
  have h := congrArg Under.Hom.right (axisRight_smashQuotient (adjoin X) (adjoin Y))
  rw [Under.comp_right, adjoin_axisRight, zero_right] at h
  have h' := congrArg (fun f ↦ (λ_ (Y ⨿ 𝟙_ C)).hom ≫ f) h
  simpa [adjoin, Category.assoc] using h'

/-- 元の直積から出発すると、二つの比較の合成は恒等射になる。 -/
lemma adjoinSmashInv_hom (X Y : C) :
    adjoinSmashInv X Y ≫ adjoinSmashHom X Y = 𝟙 (adjoin (X ⊗ Y)) := by
  apply (adjoinHomEquiv (X ⊗ Y) (adjoin (X ⊗ Y))).injective
  change coprod.inl ≫ (adjoinSmashInv X Y ≫ adjoinSmashHom X Y).right =
    coprod.inl ≫ Under.Hom.right (𝟙 (adjoin (X ⊗ Y)))
  simp only [Under.id_right, Under.comp_right, adjoinSmashInv, adjoinHomEquiv, Equiv.coe_fn_symm_mk,
    Under.homMk_right, coprod.inl_desc_assoc]
  rw [Category.assoc, ← Under.comp_right, smashQuotient_adjoinSmashHom]
  simp [adjoinProductMap, adjoin]

/-- smash 上でも二つの比較の合成は恒等射になる。四成分で判定する。 -/
lemma adjoinSmashHom_inv (X Y : C) :
    adjoinSmashHom X Y ≫ adjoinSmashInv X Y = 𝟙 (smash (adjoin X) (adjoin Y)) := by
  apply smash_hom_ext
  rw [smashQuotient_adjoinSmashHom_assoc, Category.comp_id]
  apply Under.UnderMorphism.ext
  change adjoinProductRaw X Y ≫ (adjoinSmashInv X Y).right =
    (smashQuotient (adjoin X) (adjoin Y)).right
  apply tensorCoprod_hom_ext
  · simp [adjoinSmashInv, adjoinHomEquiv]
  · erw [← Category.assoc, show (coprod.inl ⊗ₘ coprod.inr) ≫ adjoinProductRaw X Y =
        toUnit (X ⊗ 𝟙_ C) ≫ coprod.inr by simp [adjoinProductRaw]]
    rw [Category.assoc, show coprod.inr ≫ (adjoinSmashInv X Y).right =
        (smash (adjoin X) (adjoin Y)).hom from Under.w (adjoinSmashInv X Y)]
    simp [tensorHom_def, Category.assoc]
  · erw [← Category.assoc, show (coprod.inr ⊗ₘ coprod.inl) ≫ adjoinProductRaw X Y =
        toUnit (𝟙_ C ⊗ Y) ≫ coprod.inr by simp [adjoinProductRaw]]
    rw [Category.assoc, show coprod.inr ≫ (adjoinSmashInv X Y).right =
        (smash (adjoin X) (adjoin Y)).hom from Under.w (adjoinSmashInv X Y)]
    simp [tensorHom_def', Category.assoc]
  · erw [← Category.assoc, show (coprod.inr ⊗ₘ coprod.inr) ≫ adjoinProductRaw X Y =
        toUnit (𝟙_ C ⊗ 𝟙_ C) ≫ coprod.inr by simp [adjoinProductRaw]]
    rw [Category.assoc, show coprod.inr ≫ (adjoinSmashInv X Y).right =
        (smash (adjoin X) (adjoin Y)).hom from Under.w (adjoinSmashInv X Y)]
    simp only [tensorHom_def', Category.assoc, adjoinQuotient_basepoint_left,
      comp_toUnit_assoc]

/-- 自由な基点の追加は、直積を smash 積へ比較する同型を持つ。 -/
def adjoinSmashIso (X Y : C) : smash (adjoin X) (adjoin Y) ≅ adjoin (X ⊗ Y) where
  hom := adjoinSmashHom X Y
  inv := adjoinSmashInv X Y
  hom_inv_id := adjoinSmashHom_inv X Y
  inv_hom_id := adjoinSmashInv_hom X Y

omit [MonoidalClosed C] in
/-- 逆比較の非基点成分は、元の直積を商写像へ送る標準射。 -/
@[reassoc (attr := simp)] lemma adjoinSmashInv_first (X Y : C) :
    coprod.inl ≫ (adjoinSmashInv X Y).right =
      (coprod.inl ⊗ₘ coprod.inl) ≫ (smashQuotient (adjoin X) (adjoin Y)).right := by
  simp [adjoinSmashInv, adjoinHomEquiv]

omit [MonoidalClosed C] in
/-- 逆比較は二つの元の対象の射に関して自然。 -/
@[reassoc] lemma adjoinSmashInv_naturality {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    adjoinFunctor.map (f ⊗ₘ g) ≫ adjoinSmashInv X' Y' =
      adjoinSmashInv X Y ≫ smashMap (adjoinFunctor.map f) (adjoinFunctor.map g) := by
  apply (adjoinHomEquiv (X ⊗ Y) (smash (adjoin X') (adjoin Y'))).injective
  change coprod.inl ≫ (adjoinFunctor.map (f ⊗ₘ g) ≫ adjoinSmashInv X' Y').right =
    coprod.inl ≫ (adjoinSmashInv X Y ≫
      smashMap (adjoinFunctor.map f) (adjoinFunctor.map g)).right
  change coprod.inl ≫ (coprod.map (f ⊗ₘ g) (𝟙 (𝟙_ C)) ≫
    (adjoinSmashInv X' Y').right) = coprod.inl ≫ ((adjoinSmashInv X Y).right ≫
      (smashMap (adjoinFunctor.map f) (adjoinFunctor.map g)).right)
  erw [coprod.inl_map_assoc, adjoinSmashInv_first, adjoinSmashInv_first_assoc,
    ← Under.comp_right, smashQuotient_map, Under.comp_right, prodMap_right]
  simp [← Category.assoc, tensorHom_comp_tensorHom, adjoinFunctor]

/-- 順比較も二つの元の対象の射に関して自然。 -/
@[reassoc] lemma adjoinSmashHom_naturality {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    smashMap (adjoinFunctor.map f) (adjoinFunctor.map g) ≫ adjoinSmashHom X' Y' =
      adjoinSmashHom X Y ≫ adjoinFunctor.map (f ⊗ₘ g) := by
  apply (cancel_mono (adjoinSmashIso X' Y').inv).mp
  change (smashMap (adjoinFunctor.map f) (adjoinFunctor.map g) ≫
    adjoinSmashHom X' Y') ≫ adjoinSmashInv X' Y' =
    (adjoinSmashHom X Y ≫ adjoinFunctor.map (f ⊗ₘ g)) ≫ adjoinSmashInv X' Y'
  erw [Category.assoc, adjoinSmashHom_inv, Category.comp_id,
    Category.assoc, adjoinSmashInv_naturality, ← Category.assoc,
    adjoinSmashHom_inv, Category.id_comp]

end SerrePositivity.PointedObject
