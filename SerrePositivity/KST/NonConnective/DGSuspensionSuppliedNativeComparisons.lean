module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaNativePFamily
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
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaFamily_iso R s).precomp a

/-- P 比較も同じ D の実 Morita 全族を使用し、先行全族の追加入力を持たない。 -/
def dgSuspensionSuppliedPParameterIso
    {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ dgKInputInfinity.{u, max (u + 1) v} R) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePComparisonFamily_iso R s).precomp a

/-- 全族の端点固定境界は任意パラメータの再制限でも厳密に保持される。 -/
theorem dgSuspensionSuppliedPParameter_boundary
    {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ dgKInputInfinity.{u, max (u + 1) v} R) :
    (a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePArrowFamily R s) ≫ (pre (boundary 1).ι).app _ =
      (a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaArrowFamily R s) ≫ (pre (boundary 1).ι).app _ := by
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePArrowFamily_boundary]

/-- 同じ核角の全 ν 作用が D の終点と一致すれば、実 Morita 全比較を直接消費する。
この一致は頂点の等号ではなく全単体射の等号であり、明示入力に保持する。 -/
def dgSuspensionCoherentKernelMoritaIso (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentSquareInput R s)
    (hkernel : dgSuspensionNativeSquareCornerFamily R p.square 0 0 ≫ dgKInputNu R =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeKernelStableFamily R s) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKInputNu R)
      (dgSuspensionNativeSquareCornerFamily R p.square 0 0 ≫ dgKInputNu R) := by
  rw [hkernel]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaFamily_iso R s

/-- 反復段でも元の全作用と同じ実 Morita 比較を使う。 -/
def dgSuspensionCoherentIterationMoritaIso
    (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentSquareInput R s)
    (hkernel : dgSuspensionNativeSquareCornerFamily R p.square 0 0 ≫ dgKInputNu R =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeKernelStableFamily R s) (n : ℕ) :=
  (dgSuspensionCoherentKernelMoritaIso R s p hkernel).precomp ((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s p.action) n)

/-- 元の P 比較も同じ採用済み反復作用へ制限し、各段で比較を選び直さない。 -/
def dgSuspensionCoherentIterationPIso
    (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentSquareInput R s) (n : ℕ) :=
  dgSuspensionSuppliedPParameterIso R s ((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s p.action) n)

/-- 反復した Morita path は、元の実懸垂段の指定評価辺を厳密回収する。 -/
theorem dgSuspensionCoherentIterationMorita_at
    (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentSquareInput R s)
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    ((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s p.action) n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaFamily R s).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertex
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap R (dgSuspensionIteration R s A n)
          (s (dgSuspensionIteration R s A n)).cone
          (s (dgSuspensionIteration R s A n)).perfect))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap_isInvertible R (dgSuspensionIteration R s A n)
          (s (dgSuspensionIteration R s A n)).cone
          (s (dgSuspensionIteration R s A n)).perfect) := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaFamily R s).app (Opposite.op ⦋0⦌)
    (((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s p.action) n).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) = _
  rw [(_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration_vertex R s p.action), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaFamily_at]

/-- P 比較 path も同じ実反復段の元の指定比較である。 -/
theorem dgSuspensionCoherentIterationP_at
    (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentSquareInput R s)
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    ((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s p.action) n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePComparisonFamily R s).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePComparisonPath R (dgSuspensionIteration R s A n)
        (s (dgSuspensionIteration R s A n)).cone
        (s (dgSuspensionIteration R s A n)).perfect := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePComparisonFamily R s).app (Opposite.op ⦋0⦌)
    (((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s p.action) n).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) = _
  rw [(_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration_vertex R s p.action), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePComparisonFamily_at]

end SerrePositivity.KST.NonConnective
