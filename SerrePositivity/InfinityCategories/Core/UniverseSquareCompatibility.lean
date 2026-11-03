module
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Square
public import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.Core.UniverseOuterHornJoins
public import SerrePositivity.InfinityCategories.Core.UniverseSquareShape
public import SerrePositivity.InfinityCategories.Core.UniverseSquareTriangles

/-! # 四角形と外側ホーンの錐の宇宙整合性

概要：四角形と span/cospan の錐の同型は宇宙持ち上げと可換。
方針：二つの標準三角形上で照合し、pushout の一意性を使う。
規約：h 圏での比較ではなく実写像の等式。使われ方：普遍四角形の宇宙降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet HomotopyLimits
open scoped Simplicial

private lemma inverse_square {A B C D : SSet.{u}} (e : A ≅ B) (f : C ≅ D)
    (g : A ⟶ C) (h : B ⟶ D) (w : g ≫ f.hom = e.hom ≫ h) :
    h ≫ f.inv = e.inv ≫ g := by
  apply (cancel_epi e.hom).1
  rw [← Category.assoc, ← w, Category.assoc, f.hom_inv_id, Category.comp_id,
    ← Category.assoc, e.hom_inv_id, Category.id_comp]

/-- Cospan の錐と四角形の実同型は宇宙比較と可換。 -/
lemma uliftCospanConeIso_square :
    (SSet.uliftFunctor.{v, u}).map cospanConeSquareIso.hom ≫ uliftSquareIso.hom =
      uliftCospanConeIso.{u, v}.hom ≫ cospanConeSquareIso.hom := by
  apply (cancel_epi uliftCospanConeIso.inv).1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply cospanCone_isPushout.hom_ext
  · have ht := inverse_square (uliftStdSimplexIso.{u, v} 2)
      uliftCospanConeIso ((SSet.uliftFunctor.{v, u}).map cospanConeTriangleLeft)
      cospanConeTriangleLeft uliftCospanConeIso_left
    simp only [← Category.assoc]
    rw [ht]
    simp only [Category.assoc, ← Functor.map_comp, cospanConeSquareIso_left]
    rw [uliftSquareIso_triangle]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · have ht := inverse_square (uliftStdSimplexIso.{u, v} 2)
      uliftCospanConeIso ((SSet.uliftFunctor.{v, u}).map cospanConeTriangleRight)
      cospanConeTriangleRight uliftCospanConeIso_right
    simp only [← Category.assoc]
    rw [ht]
    simp only [Category.assoc, ← Functor.map_comp, cospanConeSquareIso_right]
    rw [uliftSquareIso_triangle]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Span の錐と四角形の実同型は宇宙比較と可換。 -/
lemma uliftSpanCoconeIso_square :
    (SSet.uliftFunctor.{v, u}).map spanCoconeSquareIso.hom ≫ uliftSquareIso.hom =
      uliftSpanCoconeIso.{u, v}.hom ≫ spanCoconeSquareIso.hom := by
  apply (cancel_epi uliftSpanCoconeIso.inv).1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply spanCocone_isPushout.hom_ext
  · have ht := inverse_square (uliftStdSimplexIso.{u, v} 2)
      uliftSpanCoconeIso ((SSet.uliftFunctor.{v, u}).map spanCoconeTriangleLeft)
      spanCoconeTriangleLeft uliftSpanCoconeIso_left
    simp only [← Category.assoc]
    rw [ht]
    simp only [Category.assoc, ← Functor.map_comp, spanCoconeSquareIso_left]
    rw [uliftSquareIso_triangle]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · have ht := inverse_square (uliftStdSimplexIso.{u, v} 2)
      uliftSpanCoconeIso ((SSet.uliftFunctor.{v, u}).map spanCoconeTriangleRight)
      spanCoconeTriangleRight uliftSpanCoconeIso_right
    simp only [← Category.assoc]
    rw [ht]
    simp only [Category.assoc, ← Functor.map_comp, spanCoconeSquareIso_right]
    rw [uliftSquareIso_triangle]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories
