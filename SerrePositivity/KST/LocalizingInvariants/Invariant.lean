module

public import SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagrams
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
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 零の安定圏の値が Sp の実際の零頂点になるという条件。 -/
def PreservesZeroCategories (E : StableInfinity.{u} ⟶ Spectra.Sp.{u}) : Prop :=
  ∀ A : StableCategory.{u}, IsZeroCategory A →
    IsZeroVertex (E.app (Opposite.op ⦋0⦌) (stableVertex A))

/-- Sp 値の ∞ 関手が、零を保ち、提示された全 Verdier 列を fiber 四角形へ送る。 -/
structure IsLocalizingInvariant (E : StableInfinity.{u} ⟶ Spectra.Sp.{u}) : Prop where
  preservesZero : PreservesZeroCategories E
  preservesVerdier (d : VerdierDiagram.{u}) : IsPullbackSquare (d.square ≫ E)

/-- 局所化不変量は実際の Sp 値 ∞ 関手を保持する。 -/
structure LocalizingInvariant where
  hom : StableInfinity.{u} ⟶ Spectra.Sp.{u}
  isLocalizing : IsLocalizingInvariant hom

namespace IsLocalizingInvariant
variable {E : StableInfinity.{u} ⟶ Spectra.Sp.{u}} (hE : IsLocalizingInvariant E)
include hE

/-- 任意の零安定頂点でも、同じ実頂点の像が零となる。 -/
lemma zero_vertex (a : StableInfinity.{u} _⦋0⦌) (ha : IsZeroCategory (stableObject a)) :
    IsZeroVertex (E.app (Opposite.op ⦋0⦌) a) := by
  have h := hE.preservesZero (stableObject a) ha
  rwa [stableVertex_object] at h

/-- Verdier 列の像の零角と四角形を、そのまま Sp の三角形として保持する。 -/
def fiberTriangle (d : VerdierDiagram.{u}) : ZeroTriangle Spectra.Sp.{u} where
  square := d.square ≫ E
  zero_corner := hE.zero_vertex _ d.zero_corner

/-- 像は Sp の d2 界面の IsFiberSequence を満たす。 -/
lemma fiberTriangle_isFiber (d : VerdierDiagram.{u}) : IsFiberSequence (hE.fiberTriangle d) :=
  hE.preservesVerdier d

end IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants
