module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPathComposition

/-!
# native roof の混合円柱の元の通常の前面

概要：元の評価自然変換の通常の円柱を同じ Kan 源関手で送る。
方針：元の二値時間と単体図式を uncurry 関手へ代入する。
規約：00 は元の図式の射、01 は元の評価、11 は同じ対象の恒等射。
使われ方：mixed coherent 図式の非終点間の全 Hom。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X : C.category} (p : U ⟶ (Functor.const I).obj X)

def frontRaw {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2) :
    Fin (n + 1) ⥤ C.category :=
  (t.monotone.functor.prod' Γ) ⋙ Functor.uncurry.obj (ComposableArrows.mk₁ p)

def frontDiagram {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2) :
    Fin (n + 1) ⥤ KanHammockCategory C := frontRaw C U p Γ t ⋙ kanHammockSourceFunctor C

lemma frontDiagram_obj_zero {n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) (hi : t i = 0) :
    (frontDiagram C U p Γ t).obj i = (kanHammockSourceFunctor C).obj (U.obj (Γ.obj i)) := by
  change (kanHammockSourceFunctor C).obj (((ComposableArrows.mk₁ p).obj (t i)).obj (Γ.obj i)) = _
  rw [hi]
  rfl

lemma frontDiagram_obj_one {n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) (hi : t i = 1) :
    (frontDiagram C U p Γ t).obj i = (kanHammockSourceFunctor C).obj X := by
  change (kanHammockSourceFunctor C).obj (((ComposableArrows.mk₁ p).obj (t i)).obj (Γ.obj i)) = _
  rw [hi]
  rfl

private lemma timeMap_zero_zero {a b : Fin 2} {i j : I} (f : i ⟶ j)
    (hab : a ≤ b) (ha : a = 0) (hb : b = 0) :
    HEq ((kanHammockSourceFunctor C).map
      ((Functor.uncurry.obj (ComposableArrows.mk₁ p)).map
        (show (a, i) ⟶ (b, j) from (homOfLE hab, f))))
        ((kanHammockSourceFunctor C).map (U.map f)) := by
  subst a
  subst b
  simp [Functor.uncurry, ComposableArrows.mk₁]

private lemma timeMap_zero_one {a b : Fin 2} {i j : I} (f : i ⟶ j)
    (hab : a ≤ b) (ha : a = 0) (hb : b = 1) :
    HEq ((kanHammockSourceFunctor C).map
      ((Functor.uncurry.obj (ComposableArrows.mk₁ p)).map
        (show (a, i) ⟶ (b, j) from (homOfLE hab, f))))
        ((kanHammockSourceFunctor C).map (p.app i)) := by
  subst a
  subst b
  simp [Functor.uncurry, ComposableArrows.mk₁]

private lemma timeMap_one_one {a b : Fin 2} {i j : I} (f : i ⟶ j)
    (hab : a ≤ b) (ha : a = 1) (hb : b = 1) :
    HEq ((kanHammockSourceFunctor C).map
      ((Functor.uncurry.obj (ComposableArrows.mk₁ p)).map
        (show (a, i) ⟶ (b, j) from (homOfLE hab, f))))
        ((kanHammockSourceFunctor C).map (𝟙 X)) := by
  subst a
  subst b
  simp [Functor.uncurry, ComposableArrows.mk₁]

lemma frontDiagram_map_zero_zero {n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hij : i ≤ j)
    (hi : t i = 0) (hj : t j = 0) :
    HEq ((frontDiagram C U p Γ t).map (homOfLE hij))
      ((kanHammockSourceFunctor C).map (U.map (Γ.map (homOfLE hij)))) := by
  exact timeMap_zero_zero C U p (Γ.map (homOfLE hij)) (t.monotone hij) hi hj

lemma frontDiagram_map_zero_one {n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hij : i ≤ j)
    (hi : t i = 0) (hj : t j = 1) :
    HEq ((frontDiagram C U p Γ t).map (homOfLE hij))
      ((kanHammockSourceFunctor C).map (p.app (Γ.obj i))) := by
  exact timeMap_zero_one C U p (Γ.map (homOfLE hij)) (t.monotone hij) hi hj

lemma frontDiagram_map_one_one {n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hij : i ≤ j)
    (hi : t i = 1) (hj : t j = 1) :
    HEq ((frontDiagram C U p Γ t).map (homOfLE hij))
      (𝟙 ((kanHammockSourceFunctor C).obj X)) := by
  have h := timeMap_one_one C U p (Γ.map (homOfLE hij)) (t.monotone hij) hi hj
  exact h.trans (heq_of_eq ((kanHammockSourceFunctor C).map_id X))

end SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
