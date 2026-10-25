module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonRoundSimplexShape
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonParityFaces

/-!
概要：一巡の左右の全包含を、指定標準前置面の後続へ接続する。
方針：元の全包含の可換式を join の自然性で延ばす。
規約：全射の等式を保持する。使われ方：全比較列の偶数・奇数面の帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact
variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {C : SSet.{u + 1}} [Quasicategory C]
  {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁}
  {hD₀ : ∀ i : I₀ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i))}
  {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
variable (r : ComparisonRound hD₀ s)
  (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))

/-- 左側の全包含の可換式は、元の同じ全一巡の後にも成り立つ。 -/
lemma ComparisonRound.left_face_successor {d n : ℕ}
    (e : s.shape ≅ (Δ[d] : SSet.{u})) (l : s.left_shape ≅ (Δ[n] : SSet.{u}))
    (a : (Δ[n] : SSet.{u}) ⟶ Δ[d]) (a' : (Δ[n + 1] : SSet.{u}) ⟶ Δ[d + 2])
    (h : s.left_inclusion ≫ e.hom = l.hom ≫ a)
    (ha : (joinStdSimplexIso n 0).hom ≫ a' =
      joinMap a (𝟙 Δ[0]) ≫ joinInl (join Δ[d] Δ[0]) Δ[0] ≫ (doubleConeSimplexIso d).hom) :
    (r.next hD₁).left_inclusion ≫ (r.simplexShapeIso hD₁ e).hom =
      (oneConeSimplexIso l).hom ≫ a' := by
  change joinMap s.left_inclusion (𝟙 Δ[0]) ≫
    joinInl (join s.shape Δ[0]) Δ[0] ≫
      (joinMap (joinMap e.hom (𝟙 Δ[0])) (𝟙 Δ[0]) ≫ (doubleConeSimplexIso d).hom) = _
  rw [joinInl_joinMap_assoc]
  rw [← Category.assoc (joinMap s.left_inclusion (𝟙 Δ[0])) (joinMap e.hom (𝟙 Δ[0])),
    ← joinMap_comp, h]
  change joinMap (l.hom ≫ a) (𝟙 Δ[0] ≫ 𝟙 Δ[0]) ≫ _ = _
  rw [joinMap_comp, Category.assoc, ← ha]
  rfl

/-- 右側の全包含についても、元の旧形状を残して最後の頂点を加える式に従う。 -/
lemma ComparisonRound.right_face_successor {d n : ℕ}
    (e : s.shape ≅ (Δ[d] : SSet.{u})) (l : s.right_shape ≅ (Δ[n] : SSet.{u}))
    (a : (Δ[n] : SSet.{u}) ⟶ Δ[d]) (a' : (Δ[n + 1] : SSet.{u}) ⟶ Δ[d + 2])
    (h : s.right_inclusion ≫ e.hom = l.hom ≫ a)
    (ha : (joinStdSimplexIso n 0).hom ≫ a' =
      joinMap (a ≫ joinInl Δ[d] Δ[0]) (𝟙 Δ[0]) ≫ (doubleConeSimplexIso d).hom) :
    (r.next hD₁).right_inclusion ≫ (r.simplexShapeIso hD₁ e).hom =
      (oneConeSimplexIso l).hom ≫ a' := by
  change joinMap (s.right_inclusion ≫ joinInl s.shape Δ[0]) (𝟙 Δ[0]) ≫
    (joinMap (joinMap e.hom (𝟙 Δ[0])) (𝟙 Δ[0]) ≫ (doubleConeSimplexIso d).hom) = _
  rw [← Category.assoc, ← joinMap_comp]
  rw [Category.assoc s.right_inclusion, joinInl_joinMap, ← Category.assoc, h]
  change joinMap ((l.hom ≫ a) ≫ joinInl Δ[d] Δ[0]) (𝟙 Δ[0] ≫ 𝟙 Δ[0]) ≫ _ = _
  rw [Category.assoc l.hom, joinMap_comp, Category.assoc, ← ha]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
