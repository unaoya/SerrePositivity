module
public import SerrePositivity.KST.SConstruction.FundamentalGroupoidEquivalence

/-! # Kan 置換後の道を元の辺の逆と合成で扱う帰納法
概要：元の辺について成り立ち、逆と合成で閉じる性質を、Kan 置換後の全ての道へ移す。
方針：元の基本亜群の表示と比較の充満性を用いる。
規約：始点・終点は元の頂点の像。使われ方：元の K 対象類による零次群の生成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 元の辺と二単体の基本亜群では、元の辺・逆・合成についての帰納法が使える。 -/
lemma simplicialFundamentalGroupoid_hom_rec (A : SSet.{u})
    {P : ∀ {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplicialFundamentalGroupoid A}, (x ⟶ y) → Prop}
    (hedge : ∀ {x y : A _⦋0⦌} (e : A.Edge x y),
      P (FreeGroupoid.homMk (SSet.HomotopyCategory.homMk e)))
    (hinv : ∀ {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplicialFundamentalGroupoid A} (f : x ⟶ y), P f → P (inv f))
    (hcomp : ∀ {x y z : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplicialFundamentalGroupoid A} (f : x ⟶ y) (g : y ⟶ z),
      P f → P g → P (f ≫ g))
    {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplicialFundamentalGroupoid A} (f : x ⟶ y) : P f := by
  induction f using FreeGroupoid.hom_rec with
  | homMk f =>
    induction f using SSet.HomotopyCategory.hom_rec with
    | homMk e => exact hedge e
    | comp f g hf hg =>
      change P ((FreeGroupoid.of (hoFunctor.obj A)).map (f ≫ g))
      rw [CategoryTheory.Functor.map_comp]
      exact hcomp _ _ hf hg
  | inv f hf => exact hinv f hf
  | comp f g hf hg => exact hcomp f g hf hg

/-- Kan 値 anodyne 射の後の元の二頂点間の道は、元の辺・逆・合成による帰納法で扱える。 -/
lemma kanAnodyne_hom_rec {A B : SSet.{u}} [KanComplex B] (i : A ⟶ B)
    (hi : anodyneExtensions i)
    {P : ∀ {x y : hoFunctor.obj B}, (x ⟶ y) → Prop}
    (hedge : ∀ {x y : A _⦋0⦌} (e : A.Edge x y),
      P ((hoFunctor.map i).toFunctor.map (SSet.HomotopyCategory.homMk e)))
    (hinv : ∀ {x y : hoFunctor.obj B} (f : x ⟶ y), P f → P (inv f))
    (hcomp : ∀ {x y z : hoFunctor.obj B} (f : x ⟶ y) (g : y ⟶ z),
      P f → P g → P (f ≫ g))
    (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplicialFundamentalGroupoid A)
    (f : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i).obj x ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i).obj y) : P f := by
  obtain ⟨a, rfl⟩ := fundamentalGroupoidComparison_map_surjective i hi x y f
  apply simplicialFundamentalGroupoid_hom_rec A (P := fun a =>
    P ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i).map a)) (f := a)
  · intro x y e
    have he := CategoryTheory.Functor.congr_hom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison_fac i)
      (SSet.HomotopyCategory.homMk e)
    exact he.symm ▸ hedge e
  · intro x y a ha
    rw [CategoryTheory.Functor.map_inv]
    exact hinv _ ha
  · intro x y z a b ha hb
    rw [CategoryTheory.Functor.map_comp]
    exact hcomp _ _ ha hb

end SerrePositivity.KST.SConstruction
