module

public import SerrePositivity.InfinityCategories.F1.MarkedCocartesianFunctorFamilyLaws
public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionColimitFamily

/-!
概要：指定辺を保つ相対関手の整合する族を、余極限上の元の射へ貼る。
方針：指定辺を保つ前合成と uncurry の可換性を使い、直積の余極限へ降下する。
規約：各項の指定辺と元の相対 Hom の全パラメーターを保持する。
使われ方：cocartesian Hom の指定辺の条件を回収する前の全空間の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {J : Type v} [Category.{w} J] {T E B : SSet.{u}} (q : E ⟶ B) (D : J ⥤ Over B)
  (W : ∀ j, Set ((D.obj j).left _⦋1⦌))
  (hW : ∀ {j k} (f : j ⟶ k) e, e ∈ W j → (D.map f).left.app (Opposite.op ⦋1⦌) e ∈ W k)
  (s : ∀ j, T ⟶ markedCocartesianFunctorSpace q (D.obj j).hom (W j))
  (hs : ∀ {j k} (f : j ⟶ k), s j =
    s k ≫ markedCocartesianFunctorPre q (D.map f) (W j) (W k) (hW f))

/-- 各項の指定辺を保つ族の展開は、同じ全空間を頂点とする余錐をなす。 -/
def markedCocartesianFamilyTensorCocone : Cocone (D ⋙ Over.forget B ⋙ tensorRight T) where
  pt := E
  ι :=
    { app j := markedCocartesianFunctorUncurry (s j)
      naturality {j k} f := by
        change ((D.map f).left ▷ T) ≫ markedCocartesianFunctorUncurry (s k) =
          markedCocartesianFunctorUncurry (s j)
        rw [← markedCocartesianFunctorUncurry_overPre q (D.map f) (W j) (W k) (hW f),
          ← hs f] }

/-- 余極限上へ、指定辺を保つ元の相対関手の族の全空間の射を貼り合わせる。 -/
def markedCocartesianFamilyColimitUncurry (c : Cocone D)
    (hc : IsColimit ((Over.forget B).mapCocone c)) : c.pt.left ⊗ T ⟶ E :=
  (cocartesianSectionTensorCocone_isColimit c hc).desc
    (markedCocartesianFamilyTensorCocone q D W hW s hs)

/-- 貼り合わせた元の射は、各項上の指定された族を厳密に回収する。 -/
lemma markedCocartesianFamilyColimitUncurry_fac (c : Cocone D)
    (hc : IsColimit ((Over.forget B).mapCocone c)) (j : J) :
    ((c.ι.app j).left ▷ T) ≫ markedCocartesianFamilyColimitUncurry q D W hW s hs c hc =
      markedCocartesianFunctorUncurry (s j) :=
  (cocartesianSectionTensorCocone_isColimit c hc).fac _ j

end SerrePositivity.InfinityCategories
