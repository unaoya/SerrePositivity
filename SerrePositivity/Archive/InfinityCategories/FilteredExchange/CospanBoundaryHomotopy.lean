module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoproductCylinderMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：二入力の指定輸送を標的の境界の指定輸送へまとめる。
方針：元の二射で写した全円柱を直和上で貼る。
規約：元の入力の全輸送と同じ底の全円柱を保持する。
使われ方：単射な境界を持つ標的の相対輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A C M E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H)
  (m : A ⨿ C ⟶ M) (r : M ⟶ H) (u : A ⟶ E) (v : C ⟶ D)
  (hm : m ≫ r = coprod.desc (u ≫ f) (v ≫ g)) (b : B _⦋0⦌)
  (s : A ⟶ vertexFiber (f ≫ p) b) (t : C ⟶ vertexFiber (g ≫ p) b)
  (Hu : SSet.Homotopy u (s ≫ vertexFiberι (f ≫ p) b))
  (Hv : SSet.Homotopy v (t ≫ vertexFiberι (g ≫ p) b))

/-- 概要：二入力の輸送は元の標的の境界の輸送を与える。
方針：元の f・g で写した全円柱を直和上で貼り、両端を計算する。
規約：h は coprodCylinderMap そのもの。使われ方：相対持ち上げの指定境界円柱。 -/
def cospanBoundaryHomotopy : SSet.Homotopy (m ≫ r)
    (coprod.desc (s ≫ vertexFiberMap (f ≫ p) p f rfl b)
      (t ≫ vertexFiberMap (g ≫ p) p g rfl b) ≫ vertexFiberι p b) where
  h := coprodCylinderMap (Hu.h ≫ f) (Hv.h ≫ g)
  h₀ := by
    change SSet.ι₀ ≫ coprodCylinderMap (Hu.h ≫ f) (Hv.h ≫ g) = m ≫ r
    simp only [coprodCylinderMap_zero, ← Category.assoc, Hu.h₀, Hv.h₀]
    exact hm.symm
  h₁ := by
    change SSet.ι₁ ≫ coprodCylinderMap (Hu.h ≫ f) (Hv.h ≫ g) =
      coprod.desc (s ≫ vertexFiberMap (f ≫ p) p f rfl b)
        (t ≫ vertexFiberMap (g ≫ p) p g rfl b) ≫ vertexFiberι p b
    rw [coprodCylinderMap_one, coprod.desc_comp]
    simp only [← Category.assoc, Hu.h₁, Hv.h₁]
    simp only [Category.assoc, vertexFiberMap_ι]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：境界の貼り合わせ円柱の底は標的の元の全円柱に厳密に一致。
方針：両枝で元の入力輸送の底の式を使う。
規約：全時刻で一致。使われ方：指定境界付きの標的の相対輸送。 -/
lemma cospanBoundaryHomotopy_projection (h : M ⊗ (Δ[1] : SSet.{u}) ⟶ B)
    (hu : Hu.h ≫ (f ≫ p) = (((coprod.inl : A ⟶ A ⨿ C) ≫ m) ▷ (Δ[1] : SSet.{u})) ≫ h)
    (hv : Hv.h ≫ (g ≫ p) = (((coprod.inr : C ⟶ A ⨿ C) ≫ m) ▷ (Δ[1] : SSet.{u})) ≫ h) :
    (cospanBoundaryHomotopy p f g m r u v hm b s t Hu Hv).h ≫ p =
      (m ▷ (Δ[1] : SSet.{u})) ≫ h := by
  apply coprodCylinder_hom_ext
  · change ((coprod.inl : A ⟶ A ⨿ C) ▷ (Δ[1] : SSet.{u})) ≫
      (coprodCylinderMap (Hu.h ≫ f) (Hv.h ≫ g) ≫ p) = _
    rw [← Category.assoc, coprodCylinderMap_inl, Category.assoc, hu,
      comp_whiskerRight, Category.assoc]
  · change ((coprod.inr : C ⟶ A ⨿ C) ▷ (Δ[1] : SSet.{u})) ≫
      (coprodCylinderMap (Hu.h ≫ f) (Hv.h ≫ g) ≫ p) = _
    rw [← Category.assoc, coprodCylinderMap_inr, Category.assoc, hv,
      comp_whiskerRight, Category.assoc]

end SerrePositivity.InfinityCategories.F2
