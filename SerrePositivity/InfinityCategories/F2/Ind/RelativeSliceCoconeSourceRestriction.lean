module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeSliceCoconeUncurry
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorPrecomposition

/-!
概要：相対 slice 関手の普遍全余錐は、元の底形状の制限と全次数で可換。
方針：全族の join と直積の比較を同じ元の射で制限する。
規約：終点写像は変更しない。使われ方：終端区間を固定する普遍族の制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- join と直積の比較は、元の左形状の任意の制限に自然。 -/
lemma joinTensorLeft_source_naturality {A K : SSet.{u}} (R B : SSet.{u}) (a : K ⟶ A) :
    (R ◁ joinMap a (𝟙 B)) ≫ joinTensorLeft R A B =
      joinTensorLeft R K B ≫ joinMap (R ◁ a) (𝟙 B) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨r, ⟨⟨_ | ℓ, hℓ⟩, x, y⟩⟩ <;> rfl

/-- 同じ底形状への制限は、普遍全余錐の相対 uncurry と厳密に可換。 -/
lemma relativeSliceCoconeUncurry_source {A K X : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X) (a : K ⟶ A) :
    (joinMap a (𝟙 (Δ[0] : SSet.{u})) ▷ relativeFunctorSpace (sliceOverProjection p) b) ≫
      relativeSliceCoconeUncurry p b =
        (join K Δ[0] ◁ relativeFunctorPre (sliceOverProjection p) b a) ≫
          relativeSliceCoconeUncurry p (a ≫ b) := by
  let R := relativeFunctorSpace (sliceOverProjection p) b
  let S := relativeFunctorSpace (sliceOverProjection p) (a ≫ b)
  let c := relativeFunctorPre (sliceOverProjection p) b a
  have hs : (joinMap a (𝟙 Δ[0]) ▷ R) ≫ (β_ (join A Δ[0]) R).hom =
      (β_ (join K Δ[0]) R).hom ≫ (R ◁ joinMap a (𝟙 Δ[0])) := by rfl
  have ht : (join K Δ[0] ◁ c) ≫ (β_ (join K Δ[0]) S).hom =
      (β_ (join K Δ[0]) R).hom ≫ (c ▷ join K Δ[0]) := by rfl
  have hc : (c ▷ K) ≫ relativeSliceCoconeLeft p (a ≫ b) =
      (R ◁ a) ≫ relativeSliceCoconeLeft p b := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨r, k⟩
    rfl
  have he : joinMap (c ▷ K) (𝟙 Δ[0]) ≫
      sliceOverUncurry (relativeSliceCoconeLeft p (a ≫ b)) =
        joinMap (R ◁ a) (𝟙 Δ[0]) ≫ sliceOverUncurry (relativeSliceCoconeLeft p b) := by
    rw [← sliceOverUncurry_precomp, ← sliceOverUncurry_precomp, hc]
  rw [relativeSliceCoconeUncurry, ← Category.assoc, hs]
  simp only [Category.assoc]
  rw [← Category.assoc (R ◁ joinMap a (𝟙 Δ[0])), joinTensorLeft_source_naturality]
  simp only [Category.assoc]
  rw [relativeSliceCoconeUncurry, ← Category.assoc (join K Δ[0] ◁ c), ht]
  simp only [Category.assoc]
  rw [← Category.assoc (c ▷ join K Δ[0]), joinTensorLeft_naturality]
  simp only [Category.assoc]
  rw [he]

end SerrePositivity.InfinityCategories.F2.Ind
