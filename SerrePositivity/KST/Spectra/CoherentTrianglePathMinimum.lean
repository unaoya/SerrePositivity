module

public import SerrePositivity.KST.Spectra.CoherentPathParameters
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.CoherentPathMinimum

/-!
概要：二単体の長い Hom の区間座標と、weighted cone の反転最小点座標を照合する。
方針：内点を含まない時は最小正点が終点、含む時は内点になることを計算する。
規約：係数の反転と区間の反転同型を明示。使われ方：weighted cone の元の三角形の読取り。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates

/-- 長い path の最初の正頂点は、元の内点フラグの反転座標。 -/
lemma triangleFlaggedPath_minimum (a : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum (j := (1 : Fin 2)) (flaggedPath.{u} (fun _ : Fin 1 ↦ a)) = a.rev := by
  fin_cases a
  · let k := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum (j := (1 : Fin 2)) (flaggedPath.{u} (fun _ : Fin 1 ↦ 0))
    have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum_mem (j := (1 : Fin 2))
      (flaggedPath.{u} (fun _ : Fin 1 ↦ 0))
    change k.succ = 0 ∨ k.succ = Fin.last 2 ∨
      ∃ r : Fin 1, k.succ = r.succ.castSucc ∧ (0 : Fin 2) = 1 at hm
    apply Fin.ext
    change k.val = 1
    rcases hm with h | h | ⟨_, _, h⟩
    · have hv := congrArg Fin.val h
      change k.val + 1 = 0 at hv
      omega
    · have hv := congrArg Fin.val h
      change k.val + 1 = 2 at hv
      omega
    · exact (by decide : (0 : Fin 2) ≠ 1) h |>.elim
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum (j := (1 : Fin 2))
      (flaggedPath.{u} (fun _ : Fin 1 ↦ 1)) = 0
    apply le_antisymm ?_ (Fin.zero_le _)
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum_le
    exact Or.inr (Or.inr ⟨0, rfl, rfl⟩)

/-- 初区間の添字に制限しても、同じ反転座標になる。 -/
lemma triangleFlaggedPath_minimumIndex (a : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumIndex (j := (1 : Fin 2)) (flaggedPath.{u} (fun _ : Fin 1 ↦ a)) = a.rev := by
  apply Fin.ext
  exact congrArg Fin.val (triangleFlaggedPath_minimum a)

/-- weighted cone の最小点の反転を標準区間へ戻すと、元の path 区間そのもの。 -/
lemma trianglePathInterval_minimum_reverse :
    trianglePathInterval.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap (1 : Fin 2) ≫
      (stdSimplex.opIso ⦋1⦌).hom = 𝟙 (Δ[1] : SSet.{u}) := by
  change trianglePathInterval ≫ (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumReverseFunctor (1 : Fin 2)) ≫
    (stdSimplex.isoNerve 1).inv ≫ (stdSimplex.opIso ⦋1⦌).inv) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.ext
  intro i
  change ((stdSimplex.isoNerve 1).inv.app (Opposite.op ⦋n⦌)
    ((nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumReverseFunctor (1 : Fin 2))).app (Opposite.op ⦋n⦌)
      (trianglePathInterval.app (Opposite.op ⦋n⦌) a))) i = a i
  rw [stdSimplex.isoNerve_inv_app_apply.{u}]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumIndex (j := (1 : Fin 2))
    (flaggedPath (fun _ : Fin 1 ↦ a i))).rev = a i
  rw [triangleFlaggedPath_minimumIndex, Fin.rev_rev]

/-- 元の path 区間から反転した標準区間への最小点の射は、標準の反転同型の逆。 -/
lemma trianglePathInterval_minimum :
    trianglePathInterval.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap (1 : Fin 2) =
      (stdSimplex.opIso ⦋1⦌).inv := by
  apply (cancel_mono (stdSimplex.opIso ⦋1⦌).hom).mp
  rw [Category.assoc, trianglePathInterval_minimum_reverse, Iso.inv_hom_id]

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
