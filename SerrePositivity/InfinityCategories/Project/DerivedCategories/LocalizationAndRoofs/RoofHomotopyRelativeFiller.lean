module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-! # 全境界付きのホモトピー相対充填

概要：厳密な比較正方形の充填を、境界と商像の全時刻の整合性を保って表す。
方針：実充填と二つの実ホモトピーおよびその境界等式を束ねる。
規約：境界のホモトピーを定値とは要求しない。使われ方：屋根比較の弱同値判定。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 実充填の境界と商像を、全境界・全時刻で厳密に整合させた相対充填。 -/
structure RoofHomotopyRelativeFiller {L K E Q : SSet.{u}} (i : L ⟶ K) (F : E ⟶ Q)
    (a : L ⟶ E) (g : K ⟶ Q) where
  filler : K ⟶ E
  boundary : SSet.Homotopy (i ≫ filler) a
  comparison : SSet.Homotopy (filler ≫ F) g
  compatibility : (i ▷ (Δ[1] : SSet.{u})) ≫ comparison.h = boundary.h ≫ F

end SerrePositivity.InfinityCategories.Project.DerivedCategories
