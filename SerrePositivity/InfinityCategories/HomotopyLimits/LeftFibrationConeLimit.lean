module

public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationTerminalLift
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeHomTerminalBoundary
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeHomBoundaryFiber
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorExtensionSpace
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitCriterion

/-!
概要：底の極限錐を持ち上げた同じ錐は、全延長空間が可縮なら全空間でも極限。
方針：相対内部 Hom の fiber を元の延長空間へ同定し、終点境界充填を合成する。
規約：元の図式・同じ全錐・同じ射影を保持する。
使われ方：有限積保存する前層の小さい元の圏の有限積と、その反転の有限余積。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 底で極限となる同じ錐は、元の全延長空間が可縮なら全空間でも極限。 -/
lemma isLimitCone_of_leftFibration_extension
    {K E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    {d : K ⟶ E} (a : JoinCone d) (ha : IsLimitCone (mapJoinCone p a))
    (h : IsContractibleKan (relativeFunctorExtensionSpace p (a.val ≫ p)
      (joinInr (Δ[0] : SSet.{u}) K) d (by rw [← Category.assoc, a.property]))) :
    IsLimitCone a := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  have : Quasicategory ((internalHom.obj (Opposite.op K)).obj E) :=
    inferInstanceAs (Quasicategory ((ihom K).obj E))
  have : Quasicategory
      ((internalHom.obj (Opposite.op (join (Δ[0] : SSet.{u}) K))).obj E) :=
    inferInstanceAs (Quasicategory ((ihom (join (Δ[0] : SSet.{u}) K)).obj E))
  let i := joinInr (Δ[0] : SSet.{u}) K
  let r := Functor.PullbackObjObj.ofHasPullback internalHom i p
  have : InnerFibration r.fst :=
    ⟨innerFibrations.of_isPullback r.isPullback.flip
      (InnerFibration.mem (q := (pre i).app B))⟩
  have : Quasicategory r.pt := quasicategory_of_innerFibration r.fst
  have : LeftFibration r.π := leftFibration_pullbackObjObjπ i p r
  have := leftFibration_cocartesianHornStructure r.π
  let x := functorVertex a.val
  let z := r.π.app (Opposite.op ⦋0⦌) x
  have hz₀ : r.fst.app (Opposite.op ⦋0⦌) z = functorVertex d := by
    change (r.π ≫ r.fst).app (Opposite.op ⦋0⦌) x = _
    rw [r.π_fst]
    change functorVertex (joinInr (Δ[0] : SSet.{u}) K ≫ a.val) = _
    rw [a.property]
  have hz₁ : r.snd.app (Opposite.op ⦋0⦌) z = functorVertex (a.val ≫ p) := by
    change (r.π ≫ r.snd).app (Opposite.op ⦋0⦌) x = _
    rw [r.π_snd]
    rfl
  let e := relativeHomBoundaryFiberIso i p r (a.val ≫ p) d
    (by rw [← Category.assoc, a.property]) z hz₀ hz₁
  have hf : IsContractibleKan (vertexFiber r.π z) :=
    (qCatEquivalenceOfIso e).isContractibleKan_iff.mpr h
  let v : (vertexFiber r.π z) _⦋0⦌ := ⟨x, (pinchedConstant_zero z).symm⟩
  have ht := terminalBoundaryLifting_of_isTerminalVertex_fiber r.π z v
    (hf.isTerminalVertex v)
  apply isLimitCone_of_terminalBoundaryLifting_coneRestriction a
  apply terminalBoundaryLifting_pre_of_relativeHom i p r x ht
  exact terminalBoundaryLifting_coneRestriction_of_isLimitCone (mapJoinCone p a) ha

end SerrePositivity.InfinityCategories.HomotopyLimits
