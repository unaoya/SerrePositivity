module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorColimitLift

/-!
概要：指定辺を保つ相対 Hom の族の貼り合わせは、各項を厳密に回収し一意。
方針：指定辺を保つ前合成の展開と、直積上の余極限の普遍性で検証する。
規約：各脚は指定辺を保ち、全体の指定辺は各項の指定辺で覆われる。
使われ方：元の cocartesian Hom の高次の降下と、その core への移送。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {J : Type v} [Category.{w} J] {T E B : SSet.{u}} (q : E ⟶ B) (D : J ⥤ Over B)
  (W : ∀ j, Set ((D.obj j).left _⦋1⦌))
  (hW : ∀ {j k} (f : j ⟶ k) e, e ∈ W j → (D.map f).left.app (Opposite.op ⦋1⦌) e ∈ W k)
  (s : ∀ j, T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q (D.obj j).hom (W j))
  (hs : ∀ {j k} (f : j ⟶ k), s j =
    s k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q (D.map f) (W j) (W k) (hW f))
  (c : Cocone D) (hc : IsColimit ((Over.forget B).mapCocone c))
  (U : Set (c.pt.left _⦋1⦌))
  (hU : ∀ e ∈ U, ∃ j t, t ∈ W j ∧ (c.ι.app j).left.app (Opposite.op ⦋1⦌) t = e)
  (hi : ∀ j e, e ∈ W j → (c.ι.app j).left.app (Opposite.op ⦋1⦌) e ∈ U)

/-- 貼った相対 Hom の族を展開すると、元の直積上の貼り合わせの図式になる。 -/
lemma markedCocartesianFamilyColimitLift_uncurry :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFamilyColimitLift q D W hW s hs c hc U hU) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFamilyColimitUncurry q D W hW s hs c hc :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorUncurry_curry _ _ _ _

/-- 貼り合わせた同じ相対 Hom の族は、各項上の元の族を厳密に回収する。 -/
lemma markedCocartesianFamilyColimitLift_fac (j : J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFamilyColimitLift q D W hW s hs c hc U hU ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q (c.ι.app j) (W j) U (hi j) = s j := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorUncurry_injective q (D.obj j).hom (W j)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorUncurry_overPre,
    markedCocartesianFamilyColimitLift_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFamilyColimitUncurry_fac]

/-- 各項で指定された同じ族を回収する元の相対 Hom の族は一意。 -/
lemma markedCocartesianFamilyColimitLift_unique
    (m : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q c.pt.hom U)
    (hm : ∀ j, m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q (c.ι.app j) (W j) U (hi j) = s j) :
    m = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFamilyColimitLift q D W hW s hs c hc U hU := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorUncurry_injective q c.pt.hom U
  rw [markedCocartesianFamilyColimitLift_uncurry]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionTensorCocone_isColimit c hc).hom_ext
  intro j
  change ((c.ι.app j).left ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorUncurry m =
    ((c.ι.app j).left ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFamilyColimitUncurry q D W hW s hs c hc
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorUncurry_overPre q (c.ι.app j) (W j) U (hi j), hm j,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFamilyColimitUncurry_fac]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
