module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSequence

/-!
概要：全空間のホモトピー群が自明な fiber 列の正次数の連結同型。
方針：構成済みの長完全列と連結準同型から単射性・全射性を導く。
規約：ここでは標的が正次数の群である部分を扱う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。path fibration による次数移動。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

variable {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] [KanComplex E] [KanComplex B]
  (e : E _⦋0⦌) (n : ℕ)
  [Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup E n e)] [Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup E (n + 1) e)]

/-- 概要：全空間の隣接二次数が自明なら連結準同型は全単射。
方針：長完全列の底の完全性で核を消し、fiber の完全性で全射性を得る。
規約：fiber の実際の次数は n + 1。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の正次数の同型。 -/
theorem connectingHom_bijective_of_total_subsingleton :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom p e n) := by
  constructor
  · apply (injective_iff_map_eq_one (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom p e n)).2
    intro a ha
    obtain ⟨b, hb⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_total_base p e n a).1 ha
    have hb0 : b = 1 := Subsingleton.elim _ _
    rw [hb0, MonoidHom.map_one] at hb
    exact hb.symm
  · intro a
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_connecting_fiber p e n a).1 (Subsingleton.elim _ _)

/-- 概要：全空間の隣接二次数が自明な場合の連結群同型。
方針：連結準同型の全単射性を群同型へ束ねる。
規約：底の次数 n + 2 から fiber の次数 n + 1。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の次数移動。 -/
noncomputable def connectingHomEquivOfTotalSubsingleton :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B (n + 1) (p.app _ e) ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)) n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) :=
  MulEquiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom p e n) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom_bijective_of_total_subsingleton p e n)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
