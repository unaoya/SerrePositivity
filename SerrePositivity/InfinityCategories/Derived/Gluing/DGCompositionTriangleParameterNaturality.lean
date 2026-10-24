module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionTriangleFamily
/-! # 同じ標準合成三角形の全入力自然性

概要：標準 coherent 合成三角形を、入力の制限を保って比較する。
方針：join のパラメーター自然性を slice の二単体へ移し、同じ coherent prism を使う。
規約：Small 仮定や三角形の再選択を導入しない。
使われ方：元 Hom 全体での native 標準面を、正本係数三角形へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet DifferentialGraded DGNerve
open scoped Simplicial
lemma dgGluingJoinParameterComparison_parameter {A B K L : SSet.{u}} (i : L ⟶ K) :
    (join A B ◁ i) ≫ dgGluingJoinParameterComparison A B K =
      dgGluingJoinParameterComparison A B L ≫ joinMap (A ◁ i) (𝟙 B) := by
  have hn : (join A B ◁ i) ≫ (β_ (join A B) K).hom =
      (β_ (join A B) L).hom ≫ (i ▷ join A B) := rfl
  have hb : (i ▷ A) ≫ (β_ K A).hom = (β_ L A).hom ≫ (A ◁ i) := rfl
  rw [dgGluingJoinParameterComparison, ← Category.assoc, hn, Category.assoc,
    reassoc_of% (joinTensorLeft_naturality i A B), ← joinMap_comp, hb, Category.id_comp]
  have hj := joinMap_comp (β_ L A).hom (A ◁ i) (𝟙 B) (𝟙 B)
  simp only [Category.id_comp] at hj
  simpa only [dgGluingJoinParameterComparison, Category.assoc] using
    congrArg (fun k => (β_ (join A B) L).hom ≫ joinTensorLeft L A B ≫ k) hj
lemma dgGluingSlicePrismTriangle_parameter {K L X : SSet.{u}} {p : (Δ[0] : SSet.{u}) ⟶ X}
    (s : (Δ[1] : SSet.{u}) ⊗ K ⟶ sliceOver p) (i : L ⟶ K) :
    (Δ[2] ◁ i) ≫ dgGluingSlicePrismTriangle s =
      dgGluingSlicePrismTriangle ((Δ[1] ◁ i) ≫ s) := by
  have hn : (Δ[2] ◁ i) ≫ ((joinStdSimplexIso 1 0).inv ▷ K) =
      ((joinStdSimplexIso 1 0).inv ▷ L) ≫ (join Δ[1] Δ[0] ◁ i) := rfl
  rw [dgGluingSlicePrismTriangle, ← Category.assoc, hn, Category.assoc,
    reassoc_of% (dgGluingJoinParameterComparison_parameter (A := Δ[1]) (B := Δ[0]) i),
    ← sliceOverUncurry_precomp]
  rfl
lemma dgGluingDGCompositionTriangleFamily_precomp (R : Type u) [CommRing R]
    (D : Type v) [DGCategory R D]
    {K L : SSet.{max u v}} {x y z : D}
    (f : K ⟶ DGNerve.pinchedHom R D x y) (g : K ⟶ DGNerve.pinchedHom R D y z)
    (i : L ⟶ K) :
    (Δ[2] ◁ i) ≫ dgGluingDGCompositionTriangleFamily R D f g =
      dgGluingDGCompositionTriangleFamily R D (i ≫ f) (i ≫ g) := by
  rw [dgGluingDGCompositionTriangleFamily, dgGluingSlicePrismTriangle_parameter,
    dgPinchedCompositionFamilyPrism_precomp]
  rfl
end SerrePositivity.InfinityCategories
