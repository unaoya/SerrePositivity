module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeInvariant

public import SerrePositivity.KST.LocalizingInvariants.Invariant

/-!
概要：提示源 S 上の局所化不変量と、ν の像が Verdier となる実四角形。
方針：全ての図式を S 内で指定し、ν と値関手を別々に後合成する。
規約：値関手の StableInfinity への延長を仮定しない。使われ方：厳密 dg 入力の K。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- ν で零となる提示頂点を同じ E の零頂点へ送る。 -/
def PreservesRelativeZeroCategories {S : SSet.{u + 1}}
    (ν : S ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) (E : S ⟶ Spectra.Sp.{u}) : Prop :=
  ∀ a : S _⦋0⦌, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (ν.app (Opposite.op ⦋0⦌) a)) →
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (E.app (Opposite.op ⦋0⦌) a)

/-- ν の像が Verdier である S 内の四角形を、E が実 fiber 四角形へ送る条件。 -/
structure IsRelativeLocalizingInvariant {S : SSet.{u + 1}}
    (ν : S ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) (E : S ⟶ Spectra.Sp.{u}) : Prop where
  preservesZero : PreservesRelativeZeroCategories ν E
  preservesVerdier (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram ν) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.square ≫ E)

/-- 提示源と値関手を保つ局所化不変量。 -/
structure RelativeLocalizingInvariant {S : SSet.{u + 1}}
    (ν : S ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) where
  hom : S ⟶ Spectra.Sp.{u}
  isLocalizing : IsRelativeLocalizingInvariant ν hom

namespace IsRelativeLocalizingInvariant
variable {S : SSet.{u + 1}} {ν : S ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}} {E : S ⟶ Spectra.Sp.{u}}
  (hE : IsRelativeLocalizingInvariant ν E)

/-- 元の S 内の四角形の値を、その零角を保って Sp の三角形とする。 -/
def fiberTriangle (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram ν) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle Spectra.Sp.{u} where
  square := d.square ≫ E
  zero_corner := hE.preservesZero _ d.zero_corner

lemma fiberTriangle_isFiber (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram ν) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence (hE.fiberTriangle d) := hE.preservesVerdier d

end IsRelativeLocalizingInvariant

/-- 既存の絶対条件は恒等提示での相対条件と同値。 -/
lemma isRelativeLocalizingInvariant_id_iff (E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Spectra.Sp.{u}) :
    IsRelativeLocalizingInvariant (𝟙 _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) E ↔ IsLocalizingInvariant E := by
  constructor
  · intro h
    refine ⟨?_, fun d => h.preservesVerdier (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram.ofAbsolute d)⟩
    intro A hA
    apply h.preservesZero (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A)
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A))
    exact hA
  · intro h
    refine ⟨fun a ha => h.zero_vertex a ha, ?_⟩
    intro d
    have hd : d.square = d.image.square := by simpa using d.image_eq
    rw [hd]
    exact h.preservesVerdier d.image

/-- 絶対不変量の制限は相対不変量。ただし逆向きの延長は要求しない。 -/
lemma IsLocalizingInvariant.relative {E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Spectra.Sp.{u}}
    (hE : IsLocalizingInvariant E) {S : SSet.{u + 1}} (ν : S ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) :
    IsRelativeLocalizingInvariant ν (ν ≫ E) := by
  refine ⟨fun a ha => hE.zero_vertex _ ha, ?_⟩
  intro d
  rw [← Category.assoc, d.image_eq]
  exact hE.preservesVerdier d.image

/-- 相対条件は提示源の変更に沿って制限できる。 -/
lemma IsRelativeLocalizingInvariant.precomp {S T : SSet.{u + 1}}
    {ν : S ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}} {E : S ⟶ Spectra.Sp.{u}}
    (hE : IsRelativeLocalizingInvariant ν E) (ρ : T ⟶ S) :
    IsRelativeLocalizingInvariant (ρ ≫ ν) (ρ ≫ E) := by
  refine ⟨fun a ha => hE.preservesZero _ ha, ?_⟩
  intro d
  let d' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram ν :=
    ⟨d.square ≫ ρ, d.image, (Category.assoc _ _ _).trans d.image_eq⟩
  exact hE.preservesVerdier d'

end SerrePositivity.KST.LocalizingInvariants
