module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagrams
public import SerrePositivity.KST.Spectra.SpectrumFiberSquares

/-!
概要：安定 ∞ 圏上の Sp 値局所化不変量の抽象条件。
方針：実際の単体的関手に零保存と Verdier 四角形の fiber 性を課す。
規約：Sp の IsStable は使わない。使われ方：具体的 K 関手の後続の局所化定理。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 零の安定圏の値が Sp の実際の零頂点になるという条件。 -/
def PreservesZeroCategories (E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Spectra.Sp.{u}) : Prop :=
  ∀ A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory A →
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (E.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A))

/-- Sp 値の ∞ 関手が、零を保ち、提示された全 Verdier 列を fiber 四角形へ送る。 -/
structure IsLocalizingInvariant (E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Spectra.Sp.{u}) : Prop where
  preservesZero : PreservesZeroCategories E
  preservesVerdier (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.square ≫ E)

/-- 局所化不変量は実際の Sp 値 ∞ 関手を保持する。 -/
structure LocalizingInvariant where
  hom : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Spectra.Sp.{u}
  isLocalizing : IsLocalizingInvariant hom

namespace IsLocalizingInvariant
variable {E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Spectra.Sp.{u}} (hE : IsLocalizingInvariant E)
include hE

/-- 任意の零安定頂点でも、同じ実頂点の像が零となる。 -/
lemma zero_vertex (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋0⦌) (ha : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject a)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (E.app (Opposite.op ⦋0⦌) a) := by
  have h := hE.preservesZero (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject a) ha
  rwa [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex_object] at h

/-- Verdier 列の像の零角と四角形を、そのまま Sp の三角形として保持する。 -/
def fiberTriangle (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle Spectra.Sp.{u} where
  square := d.square ≫ E
  zero_corner := hE.zero_vertex _ d.zero_corner

/-- 像は Sp の d2 界面の IsFiberSequence を満たす。 -/
lemma fiberTriangle_isFiber (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence (hE.fiberTriangle d) :=
  hE.preservesVerdier d

end IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Tamme "Def 16" (partial := special) "仮定：小安定圏の ∞ 圏から Sp への関手（標的をスペクトルに特殊化し、零も明示）。結論：提示された Verdier 列の像がファイバー列をなす（原典の保存条件）。"] _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
attribute [cite Tamme "Def 16" (partial := special) "仮定：小安定圏の ∞ 圏から Sp への関手（標的をスペクトルに特殊化し、零も明示）。結論：提示された Verdier 列の像がファイバー列をなす（原典の保存条件）。"] _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.fiberTriangle_isFiber
