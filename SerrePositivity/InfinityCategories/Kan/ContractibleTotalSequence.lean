module

public import SerrePositivity.InfinityCategories.Kan.FibrationSequence

/-!
概要：全空間のホモトピー群が自明な fiber 列の正次数の連結同型。
方針：構成済みの長完全列と連結準同型から単射性・全射性を導く。
規約：ここでは標的が正次数の群である部分を扱う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。path fibration による次数移動。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

variable {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] [KanComplex E] [KanComplex B]
  (e : E _⦋0⦌) (n : ℕ)
  [Subsingleton (KanHomotopyGroup E n e)] [Subsingleton (KanHomotopyGroup E (n + 1) e)]

/-- 概要：全空間の隣接二次数が自明なら連結準同型は全単射。
方針：長完全列の底の完全性で核を消し、fiber の完全性で全射性を得る。
規約：fiber の実際の次数は n + 1。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。loop の正次数の同型。 -/
theorem connectingHom_bijective_of_total_subsingleton :
    Function.Bijective (connectingHom p e n) := by
  constructor
  · apply (injective_iff_map_eq_one (connectingHom p e n)).2
    intro a ha
    obtain ⟨b, hb⟩ := (exact_total_base p e n a).1 ha
    have hb0 : b = 1 := Subsingleton.elim _ _
    rw [hb0, MonoidHom.map_one] at hb
    exact hb.symm
  · intro a
    exact (exact_connecting_fiber p e n a).1 (Subsingleton.elim _ _)

/-- 概要：全空間の隣接二次数が自明な場合の連結群同型。
方針：連結準同型の全単射性を群同型へ束ねる。
規約：底の次数 n + 2 から fiber の次数 n + 1。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。loop の次数移動。 -/
noncomputable def connectingHomEquivOfTotalSubsingleton :
    KanHomotopyGroup B (n + 1) (p.app _ e) ≃*
      KanHomotopyGroup (KanFiber p (p.app _ e)) n (fiberPoint p e) :=
  MulEquiv.ofBijective (connectingHom p e n) (connectingHom_bijective_of_total_subsingleton p e n)

end SerrePositivity.KST.Spectra
