module
public import SerrePositivity.InfinityCategories.Derived.DGKappaNativePFamily
public import SerrePositivity.KST.NonConnective.DGSuspensionCoherentSquareFamily

/-!
概要：D 正本の実 Morita・P 全族を、採用 B1 四角形の比較口へ代入する。
方針：全族を選び直さず、核角の ν 像一致だけを未供給入力に残す。
規約：頂点一致から全作用一致は推論しない。map・edgeIso・square_at の存在は別工程。
使われ方：K-7 c4・d4 の全入力比較と、同じ反復作用への再制限。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)

/-- D が実構成した全族を、任意の全高次入力パラメータへ制限した Morita 比較。 -/
def dgSuspensionSuppliedMoritaParameterIso
    {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ dgKInputInfinity.{u, max (u + 1) v} R) :=
  (dgKappaNativeMoritaFamily_iso R s).precomp a

/-- P 比較も同じ D の実 Morita 全族を使用し、先行全族の追加入力を持たない。 -/
def dgSuspensionSuppliedPParameterIso
    {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ dgKInputInfinity.{u, max (u + 1) v} R) :=
  (dgKappaNativePComparisonFamily_iso R s).precomp a

/-- 全族の端点固定境界は任意パラメータの再制限でも厳密に保持される。 -/
theorem dgSuspensionSuppliedPParameter_boundary
    {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ dgKInputInfinity.{u, max (u + 1) v} R) :
    (a ≫ dgKappaNativePArrowFamily R s) ≫ (pre (boundary 1).ι).app _ =
      (a ≫ dgKappaNativeMoritaArrowFamily R s) ≫ (pre (boundary 1).ι).app _ := by
  simp only [Category.assoc, dgKappaNativePArrowFamily_boundary]

/-- 同じ核角の全 ν 作用が D の終点と一致すれば、実 Morita 全比較を直接消費する。
この一致は頂点の等号ではなく全単体射の等号であり、明示入力に保持する。 -/
def dgSuspensionCoherentKernelMoritaIso (p : DGSuspensionCoherentSquareInput R s)
    (hkernel : dgSuspensionNativeSquareCornerFamily R p.square 0 0 ≫ dgKInputNu R =
      dgKappaNativeKernelStableFamily R s) :
    FunctorIso (dgKInputNu R)
      (dgSuspensionNativeSquareCornerFamily R p.square 0 0 ≫ dgKInputNu R) := by
  rw [hkernel]
  exact dgKappaNativeMoritaFamily_iso R s

/-- 反復段でも元の全作用と同じ実 Morita 比較を使う。 -/
def dgSuspensionCoherentIterationMoritaIso
    (p : DGSuspensionCoherentSquareInput R s)
    (hkernel : dgSuspensionNativeSquareCornerFamily R p.square 0 0 ≫ dgKInputNu R =
      dgKappaNativeKernelStableFamily R s) (n : ℕ) :=
  (dgSuspensionCoherentKernelMoritaIso R s p hkernel).precomp (p.action.iteration R s n)

/-- 元の P 比較も同じ採用済み反復作用へ制限し、各段で比較を選び直さない。 -/
def dgSuspensionCoherentIterationPIso
    (p : DGSuspensionCoherentSquareInput R s) (n : ℕ) :=
  dgSuspensionSuppliedPParameterIso R s (p.action.iteration R s n)

/-- 反復した Morita path は、元の実懸垂段の指定評価辺を厳密回収する。 -/
theorem dgSuspensionCoherentIterationMorita_at
    (p : DGSuspensionCoherentSquareInput R s)
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    (p.action.iteration R s n ≫ dgKappaNativeMoritaFamily R s).app (Opposite.op ⦋0⦌)
        (coherentNerveVertex A) =
      equivalencePathVertex
        (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (dgKappaNativeMoritaExactMap R (dgSuspensionIteration R s A n)
          (s (dgSuspensionIteration R s A n)).cone
          (s (dgSuspensionIteration R s A n)).perfect))
        (dgKappaNativeMoritaExactMap_isInvertible R (dgSuspensionIteration R s A n)
          (s (dgSuspensionIteration R s A n)).cone
          (s (dgSuspensionIteration R s A n)).perfect) := by
  change (dgKappaNativeMoritaFamily R s).app (Opposite.op ⦋0⦌)
    ((p.action.iteration R s n).app (Opposite.op ⦋0⦌) (coherentNerveVertex A)) = _
  rw [p.action.iteration_vertex, dgKappaNativeMoritaFamily_at]

/-- P 比較 path も同じ実反復段の元の指定比較である。 -/
theorem dgSuspensionCoherentIterationP_at
    (p : DGSuspensionCoherentSquareInput R s)
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    (p.action.iteration R s n ≫ dgKappaNativePComparisonFamily R s).app (Opposite.op ⦋0⦌)
        (coherentNerveVertex A) =
      dgKappaNativePComparisonPath R (dgSuspensionIteration R s A n)
        (s (dgSuspensionIteration R s A n)).cone
        (s (dgSuspensionIteration R s A n)).perfect := by
  change (dgKappaNativePComparisonFamily R s).app (Opposite.op ⦋0⦌)
    ((p.action.iteration R s n).app (Opposite.op ⦋0⦌) (coherentNerveVertex A)) = _
  rw [p.action.iteration_vertex, dgKappaNativePComparisonFamily_at]

end SerrePositivity.KST.NonConnective
