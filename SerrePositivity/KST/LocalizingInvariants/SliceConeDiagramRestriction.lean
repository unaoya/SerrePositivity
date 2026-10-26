module

public import SerrePositivity.InfinityCategories.Stable.SliceSquareDiagram

/-!
概要：実 slice から全錐図式への標準比較が、固定図式の制限と全族で可換である。
方針：join と直積の比較を右図式の射に沿って照合し、普遍錐を展開する。
規約：零単体での一致ではなく、全パラメータの単体集合の射の等式。
使われ方：実分母・次辺と標準 span 比較の左右の全辺の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- join・直積比較は、join の右図式の制限とも厳密に可換。 -/
lemma spanJoinTensorLeft_right_naturality (A B : SSet.{u}) {L J : SSet.{u}} (g : L ⟶ J) :
    (A ◁ joinMap (𝟙 B) g) ≫ joinTensorLeft A B J =
      joinTensorLeft A B L ≫ joinMap (𝟙 (A ⊗ B)) g := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, ℓ, b, c⟩
  change Join.tensorLeftSimplex A B J n
    a ⟨ℓ, Join.augHom (𝟙 B) ℓ.val b, Join.augHom g (n + 1 - ℓ.val) c⟩ =
      ⟨ℓ, Join.augHom (𝟙 (A ⊗ B)) ℓ.val
        ((Join.augTensorEquiv A B ℓ.val).symm
          (Join.augMap A (Join.prefixIncl (n + 1) ℓ.val
            (Nat.le_of_lt_succ ℓ.isLt)) a, b)),
        Join.augHom g (n + 1 - ℓ.val) c⟩
  simp only [Join.tensorLeftSimplex, Join.augHom_id]

/-- 全錐図式の比較は、普遍錐を curry した同じ射そのもの。 -/
lemma spanSliceConeDiagramMap_eq_curry {J X : SSet.{u}} (p : J ⟶ X) :
    sliceConeDiagramMap p = curry (sliceConeFamilyUncurry p) := by
  exact vertexFiberLift_ι _ _ _ _

/-- 任意のパラメータ族で、標準比較を展開すると元の普遍錐の族を回収する。 -/
lemma spanSliceConeDiagramMap_uncurry {J X T : SSet.{u}} (p : J ⟶ X)
    (F : T ⟶ sliceOver p) :
    uncurry (F ≫ sliceConeDiagramMap p) =
      (β_ (join (Δ[0] : SSet.{u}) J) T).hom ≫ joinTensorLeft T Δ[0] J ≫
        joinMap (fst T Δ[0]) (𝟙 J) ≫ sliceOverUncurry F := by
  rw [spanSliceConeDiagramMap_eq_curry, uncurry_natural_left, uncurry_curry]
  let S := sliceOver p
  let D := join (Δ[0] : SSet.{u}) J
  have hswap : (D ◁ F) ≫ (β_ D S).hom = (β_ D T).hom ≫ (F ▷ D) := rfl
  have hfst : (F ▷ (Δ[0] : SSet.{u})) ≫ fst S Δ[0] = fst T Δ[0] ≫ F := rfl
  have hjoin : joinMap (F ▷ (Δ[0] : SSet.{u})) (𝟙 J) ≫
      joinMap (fst S Δ[0]) (𝟙 J) =
      joinMap (fst T Δ[0]) (𝟙 J) ≫ joinMap F (𝟙 J) := by
    rw [← joinMap_comp, ← joinMap_comp, hfst]
  change (D ◁ F) ≫ (β_ D S).hom ≫ joinTensorLeft S Δ[0] J ≫
      joinMap (fst S Δ[0]) (𝟙 J) ≫ sliceOverUncurry (𝟙 S) = _
  rw [← Category.assoc (D ◁ F), hswap]
  simp only [Category.assoc]
  rw [← Category.assoc (F ▷ D), joinTensorLeft_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (joinMap (F ▷ (Δ[0] : SSet.{u})) (𝟙 J)), hjoin]
  simp only [Category.assoc]
  rw [← sliceOverUncurry_precomp, Category.comp_id]

/-- 標準全錐図式比較は、元の固定図式の制限を全単体で保つ。 -/
lemma spanSliceConeDiagramMap_restrict {L J X : SSet.{u}} (p : J ⟶ X) (g : L ⟶ J) :
    sliceOverRestrict p g ≫ sliceConeDiagramMap (g ≫ p) =
      sliceConeDiagramMap p ≫ (pre (joinMap (𝟙 (Δ[0] : SSet.{u})) g)).app X := by
  apply uncurry_injective
  have hr : sliceOverUncurry (sliceOverRestrict p g) =
      joinMap (𝟙 (sliceOver p)) g ≫ sliceOverUncurry (𝟙 (sliceOver p)) := by
    simpa only [Category.id_comp] using sliceOverUncurry_restrict (𝟙 (sliceOver p)) g
  rw [spanSliceConeDiagramMap_uncurry, hr,
    uncurry_pre_app, spanSliceConeDiagramMap_eq_curry, uncurry_curry]
  let S := sliceOver p
  let d := joinMap (𝟙 (Δ[0] : SSet.{u})) g
  have hswap : (d ▷ S) ≫ (β_ (join (Δ[0] : SSet.{u}) J) S).hom =
      (β_ (join (Δ[0] : SSet.{u}) L) S).hom ≫ (S ◁ d) := rfl
  have hjoin : joinMap (𝟙 (S ⊗ (Δ[0] : SSet.{u}))) g ≫
      joinMap (fst S Δ[0]) (𝟙 J) =
      joinMap (fst S Δ[0]) (𝟙 L) ≫ joinMap (𝟙 S) g := by
    simp only [← joinMap_comp, Category.id_comp, Category.comp_id]
  change _ = (d ▷ S) ≫ (β_ (join (Δ[0] : SSet.{u}) J) S).hom ≫
    joinTensorLeft S Δ[0] J ≫ joinMap (fst S Δ[0]) (𝟙 J) ≫ sliceOverUncurry (𝟙 S)
  rw [← Category.assoc (d ▷ S), hswap]
  simp only [Category.assoc]
  rw [← Category.assoc (S ◁ d), spanJoinTensorLeft_right_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (joinMap (𝟙 (S ⊗ (Δ[0] : SSet.{u}))) g), hjoin]
  simp only [Category.assoc]
  rfl

end SerrePositivity.KST.LocalizingInvariants
