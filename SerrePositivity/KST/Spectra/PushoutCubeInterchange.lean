module

public import SerrePositivity.KST.Spectra.PushoutCubePresentations

/-!
概要：立方体の二通りの反復 pushout の標準同型。
方針：三つの外側の頂点からの射の普遍性を使って両向きの射を作り、同じ三成分で逆性を示す。
規約：各包含との整合性を厳密に保持する通常の圏の同型。
使われ方：Goerss–Jardine VII §4。相対 latching と pushout-product の交換則。
-/

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Spectra.PushoutCube
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {A B X A' B' X' Y : C}
  {u : A ⟶ B} {l : A ⟶ X} {a : A ⟶ A'} {b : B ⟶ B'} {x : X ⟶ X'}
  {u' : A' ⟶ B'} {l' : A' ⟶ X'} {m : B ⟶ Y} {t : X ⟶ Y}
  (hb : u ≫ b = a ≫ u') (hx : l ≫ x = a ≫ l') (hy : u ≫ m = l ≫ t)
  {T : C} (fB : B' ⟶ T) (fX : X' ⟶ T) (fY : Y ⟶ T)
  (hA : u' ≫ fB = l' ≫ fX) (hB : b ≫ fB = m ≫ fY) (hX : x ≫ fX = t ≫ fY)

@[reassoc (attr := simp)]
lemma rightB_desc : rightB hb hx hy ≫ rightDesc hb hx hy fB fX fY hA hB hX = fB := by
  simp only [rightB, rightDesc, Category.assoc, pushout.inl_desc]
@[reassoc (attr := simp)]
lemma rightX_desc : rightX hb hx hy ≫ rightDesc hb hx hy fB fX fY hA hB hX = fX := by
  simp only [rightX, rightDesc, Category.assoc, pushout.inl_desc, pushout.inr_desc]
@[reassoc (attr := simp)]
lemma rightY_desc : rightY hb hx hy ≫ rightDesc hb hx hy fB fX fY hA hB hX = fY :=
  pushout.inr_desc _ _ _
@[reassoc (attr := simp)]
lemma leftB_desc : leftB hb hx hy ≫ leftDesc hb hx hy fB fX fY hA hB hX = fB :=
  pushout.inl_desc _ _ _
@[reassoc (attr := simp)]
lemma leftX_desc : leftX hb hx hy ≫ leftDesc hb hx hy fB fX fY hA hB hX = fX := by
  simp only [leftX, leftDesc, Category.assoc, pushout.inr_desc, pushout.inl_desc]
@[reassoc (attr := simp)]
lemma leftY_desc : leftY hb hx hy ≫ leftDesc hb hx hy fB fX fY hA hB hX = fY := by
  simp only [leftY, leftDesc, Category.assoc, pushout.inr_desc]

/-- 平行二面側からの射は三つの外側の包含で決まる。 -/
lemma right_hom_ext {f g : rightObj hb hx hy ⟶ T}
    (hB : rightB hb hx hy ≫ f = rightB hb hx hy ≫ g)
    (hX : rightX hb hx hy ≫ f = rightX hb hx hy ≫ g)
    (hY : rightY hb hx hy ≫ f = rightY hb hx hy ≫ g) : f = g := by
  apply pushout.hom_ext
  · apply pushout.hom_ext
    · simpa only [rightB, Category.assoc] using hB
    · simpa only [rightX, Category.assoc] using hX
  · exact hY

/-- 交差二面側からの射も同じ三つの外側の包含で決まる。 -/
lemma left_hom_ext {f g : leftObj hb hx hy ⟶ T}
    (hB : leftB hb hx hy ≫ f = leftB hb hx hy ≫ g)
    (hX : leftX hb hx hy ≫ f = leftX hb hx hy ≫ g)
    (hY : leftY hb hx hy ≫ f = leftY hb hx hy ≫ g) : f = g := by
  apply pushout.hom_ext
  · exact hB
  · apply pushout.hom_ext
    · simpa only [leftX, Category.assoc] using hX
    · simpa only [leftY, Category.assoc] using hY

/-- 二通りの反復 pushout は外側の三成分を保つ標準同型で結ばれる。 -/
def interchangeIso : rightObj hb hx hy ≅ leftObj hb hx hy where
  hom := rightDesc hb hx hy (leftB hb hx hy) (leftX hb hx hy) (leftY hb hx hy)
    (left_condition_A hb hx hy) (left_condition_B hb hx hy) (left_condition_X hb hx hy)
  inv := leftDesc hb hx hy (rightB hb hx hy) (rightX hb hx hy) (rightY hb hx hy)
    (right_condition_A hb hx hy) (right_condition_B hb hx hy) (right_condition_X hb hx hy)
  hom_inv_id := by
    apply right_hom_ext hb hx hy <;>
      simp [rightB, rightX, rightY, leftB, leftX, leftY, rightDesc, leftDesc, Category.assoc]
  inv_hom_id := by
    apply left_hom_ext hb hx hy <;>
      simp [rightB, rightX, rightY, leftB, leftX, leftY, rightDesc, leftDesc, Category.assoc]

/-- 交換同型は同じ三成分から作った比較射を厳密に保つ。 -/
lemma interchange_hom_desc : (interchangeIso hb hx hy).hom ≫
    leftDesc hb hx hy fB fX fY hA hB hX = rightDesc hb hx hy fB fX fY hA hB hX := by
  apply right_hom_ext hb hx hy <;>
    simp [interchangeIso, rightB, rightX, rightY, leftB, leftX, leftY,
      rightDesc, leftDesc, Category.assoc]

/-- 三つの比較射も含めた、反復 pushout の arrow 圏での交換同型。 -/
def interchangeArrowIso :
    Arrow.mk (rightDesc hb hx hy fB fX fY hA hB hX) ≅
      Arrow.mk (leftDesc hb hx hy fB fX fY hA hB hX) :=
  Arrow.isoMk (interchangeIso hb hx hy) (Iso.refl _) (by
    change (interchangeIso hb hx hy).hom ≫ leftDesc hb hx hy fB fX fY hA hB hX = _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact interchange_hom_desc hb hx hy fB fX fY hA hB hX)

end
end SerrePositivity.KST.Spectra.PushoutCube
