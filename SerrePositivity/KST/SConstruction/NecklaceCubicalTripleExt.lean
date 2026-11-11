module
public import SerrePositivity.KST.SConstruction.NecklaceCubicalDayData
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits

/-! # 三つの元の necklace 生成射による射の判定
概要：三重 Day tensor 上の射を、元の三つの全 necklace の生成射で判定する。
方針：元の各余極限の tensor 余極限を二回作り、その普遍性を使う。
規約：元の全可換三角形を保持。使われ方：mapping object 全体の結合則。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits Simplicial SSet

/-- 三つの元の全生成射の tensor は、同じ三重 tensor からの射を決定する。 -/
lemma necklaceCubicalDayTriple_hom_ext (K : SSet.{u}) (w x y z : K _⦋0⦌)
    {M : CubicalDaySet.{u}}
    {f g : (necklaceCubicalDayMapping K w x ⊗ necklaceCubicalDayMapping K x y) ⊗
      necklaceCubicalDayMapping K y z ⟶ M}
    (h : ∀ (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K w x) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z),
      ((necklaceCubicalDayCell T ⊗ₘ necklaceCubicalDayCell U) ⊗ₘ
          necklaceCubicalDayCell V) ≫ f =
        ((necklaceCubicalDayCell T ⊗ₘ necklaceCubicalDayCell U) ⊗ₘ
          necklaceCubicalDayCell V) ≫ g) : f = g := by
  apply (((necklaceCubicalDayIsColimit K w x).tensor₂
    (necklaceCubicalDayIsColimit K x y)).tensor₂
      (necklaceCubicalDayIsColimit K y z)).hom_ext
  intro p
  change (((necklaceCubicalDayCell p.1.1 ▷ necklaceCubicalDay.obj p.1.2.necklace ≫
      necklaceCubicalDayMapping K w x ◁ necklaceCubicalDayCell p.1.2) ▷
        necklaceCubicalDay.obj p.2.necklace) ≫
      (necklaceCubicalDayMapping K w x ⊗ necklaceCubicalDayMapping K x y) ◁
        necklaceCubicalDayCell p.2) ≫ f =
    (((necklaceCubicalDayCell p.1.1 ▷ necklaceCubicalDay.obj p.1.2.necklace ≫
      necklaceCubicalDayMapping K w x ◁ necklaceCubicalDayCell p.1.2) ▷
        necklaceCubicalDay.obj p.2.necklace) ≫
      (necklaceCubicalDayMapping K w x ⊗ necklaceCubicalDayMapping K x y) ◁
        necklaceCubicalDayCell p.2) ≫ g
  rw [← tensorHom_def, ← tensorHom_def]
  exact h p.1.1 p.1.2 p.2

end SerrePositivity.KST.SConstruction
