module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.MarkedCocartesianFunctorColimitLift

/-!
概要：指定辺を保つ相対 Hom の族の貼り合わせは、各項を厳密に回収し一意。
方針：指定辺を保つ前合成の展開と、直積上の余極限の普遍性で検証する。
規約：各脚は指定辺を保ち、全体の指定辺は各項の指定辺で覆われる。
使われ方：元の cocartesian Hom の高次の降下と、その core への移送。
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
  (c : Cocone D) (hc : IsColimit ((Over.forget B).mapCocone c))
  (U : Set (c.pt.left _⦋1⦌))
  (hU : ∀ e ∈ U, ∃ j t, t ∈ W j ∧ (c.ι.app j).left.app (Opposite.op ⦋1⦌) t = e)
  (hi : ∀ j e, e ∈ W j → (c.ι.app j).left.app (Opposite.op ⦋1⦌) e ∈ U)

/-- 貼った相対 Hom の族を展開すると、元の直積上の貼り合わせの図式になる。 -/
lemma markedCocartesianFamilyColimitLift_uncurry :
    markedCocartesianFunctorUncurry (markedCocartesianFamilyColimitLift q D W hW s hs c hc U hU) =
      markedCocartesianFamilyColimitUncurry q D W hW s hs c hc :=
  markedCocartesianFunctorUncurry_curry _ _ _ _

/-- 貼り合わせた同じ相対 Hom の族は、各項上の元の族を厳密に回収する。 -/
lemma markedCocartesianFamilyColimitLift_fac (j : J) :
    markedCocartesianFamilyColimitLift q D W hW s hs c hc U hU ≫
      markedCocartesianFunctorPre q (c.ι.app j) (W j) U (hi j) = s j := by
  apply markedCocartesianFunctorUncurry_injective q (D.obj j).hom (W j)
  rw [markedCocartesianFunctorUncurry_overPre,
    markedCocartesianFamilyColimitLift_uncurry, markedCocartesianFamilyColimitUncurry_fac]

/-- 各項で指定された同じ族を回収する元の相対 Hom の族は一意。 -/
lemma markedCocartesianFamilyColimitLift_unique
    (m : T ⟶ markedCocartesianFunctorSpace q c.pt.hom U)
    (hm : ∀ j, m ≫ markedCocartesianFunctorPre q (c.ι.app j) (W j) U (hi j) = s j) :
    m = markedCocartesianFamilyColimitLift q D W hW s hs c hc U hU := by
  apply markedCocartesianFunctorUncurry_injective q c.pt.hom U
  rw [markedCocartesianFamilyColimitLift_uncurry]
  apply (cocartesianSectionTensorCocone_isColimit c hc).hom_ext
  intro j
  change ((c.ι.app j).left ▷ T) ≫ markedCocartesianFunctorUncurry m =
    ((c.ι.app j).left ▷ T) ≫ markedCocartesianFamilyColimitUncurry q D W hW s hs c hc
  rw [← markedCocartesianFunctorUncurry_overPre q (c.ι.app j) (W j) U (hi j), hm j,
    markedCocartesianFamilyColimitUncurry_fac]

end SerrePositivity.InfinityCategories
