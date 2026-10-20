module

public import SerrePositivity.InfinityCategories.F1.MarkedCocartesianFunctorCoreColimitLift

/-!
概要：指定辺を保つ元の Hom の core の貼り合わせは、各項を厳密に回収し一意。
方針：core の包含で比較し、指定辺を保つ相対 Hom の貼り合わせの普遍性を使う。
規約：可逆な変換の全高次を同じ元の族として回収する。
使われ方：元の cocartesian Hom の降下と区間 Hom 比較への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {J : Type v} [Category.{w} J] [Small.{u} J]
  {T E B : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [InnerFibration q] (D : J ⥤ Over B)
  (W : ∀ j, Set ((D.obj j).left _⦋1⦌))
  (hW : ∀ {j k} (f : j ⟶ k) e, e ∈ W j → (D.map f).left.app (Opposite.op ⦋1⦌) e ∈ W k)
  (s : ∀ j, T ⟶ (quasicategoryCore
    (markedCocartesianFunctorSpace q (D.obj j).hom (W j)) : SSet.{u}))
  (hs : ∀ {j k} (f : j ⟶ k), s j = s k ≫ quasicategoryCoreMap
    (markedCocartesianFunctorPre q (D.map f) (W j) (W k) (hW f)))
  (c : Cocone D) (hc : IsColimit ((Over.forget B).mapCocone c)) (U : Set (c.pt.left _⦋1⦌))
  (hU : ∀ e ∈ U, ∃ j t, t ∈ W j ∧ (c.ι.app j).left.app (Opposite.op ⦋1⦌) t = e)
  (hi : ∀ j e, e ∈ W j → (c.ι.app j).left.app (Opposite.op ⦋1⦌) e ∈ U)

/-- core の包含後は、指定辺を保つ元の Hom の族の貼り合わせそのもの。 -/
lemma markedCocartesianCoreFamilyColimitLift_ι :
    markedCocartesianCoreFamilyColimitLift q D W hW s hs c hc U hU hi ≫
      (quasicategoryCore (markedCocartesianFunctorSpace q c.pt.hom U)).ι =
    markedCocartesianFamilyColimitLift q D W hW
      (fun j ↦ s j ≫ (quasicategoryCore
        (markedCocartesianFunctorSpace q (D.obj j).hom (W j))).ι)
      (markedCocartesianCoreFamily_underlying_compatible q D W hW s hs) c hc U hU := by
  unfold markedCocartesianCoreFamilyColimitLift
  exact quasicategoryCoreLift_ι _ _

/-- 貼り合わせた同じ core の族は、各項上の元の core の族を厳密に回収する。 -/
lemma markedCocartesianCoreFamilyColimitLift_fac (j : J) :
    markedCocartesianCoreFamilyColimitLift q D W hW s hs c hc U hU hi ≫
      quasicategoryCoreMap (markedCocartesianFunctorPre q (c.ι.app j) (W j) U (hi j)) = s j := by
  apply (cancel_mono (quasicategoryCore
    (markedCocartesianFunctorSpace q (D.obj j).hom (W j))).ι).mp
  rw [Category.assoc, quasicategoryCoreMap_ι, ← Category.assoc,
    markedCocartesianCoreFamilyColimitLift_ι]
  exact markedCocartesianFamilyColimitLift_fac q D W hW _ _ c hc U hU hi j

/-- 各項で指定された同じ core の族を回収する、元の全体上の族は一意。 -/
lemma markedCocartesianCoreFamilyColimitLift_unique
    (m : T ⟶ (quasicategoryCore (markedCocartesianFunctorSpace q c.pt.hom U) : SSet.{u}))
    (hm : ∀ j, m ≫ quasicategoryCoreMap
      (markedCocartesianFunctorPre q (c.ι.app j) (W j) U (hi j)) = s j) :
    m = markedCocartesianCoreFamilyColimitLift q D W hW s hs c hc U hU hi := by
  apply (cancel_mono (quasicategoryCore (markedCocartesianFunctorSpace q c.pt.hom U)).ι).mp
  rw [markedCocartesianCoreFamilyColimitLift_ι]
  apply markedCocartesianFamilyColimitLift_unique (hi := hi)
  intro j
  have h := congrArg (fun k ↦ k ≫ (quasicategoryCore
    (markedCocartesianFunctorSpace q (D.obj j).hom (W j))).ι) (hm j)
  rwa [Category.assoc, quasicategoryCoreMap_ι, ← Category.assoc] at h

end SerrePositivity.InfinityCategories
