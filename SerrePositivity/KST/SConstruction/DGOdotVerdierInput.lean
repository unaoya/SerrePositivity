module
public import SerrePositivity.KST.SConstruction.DGOdotInputTriangle
public import SerrePositivity.KST.SConstruction.DGOdotTargetCone
public import SerrePositivity.KST.SConstruction.DGKRelativeInvariant

/-!
概要：元の dg 対角と同じ実商射を固定 S に置き、β3 の接続証拠を分離する。
方針：同じ対象宇宙への持ち上げを使い、Sp 正本の Verdier 条件へ証拠を渡す。
規約：核一致と cofiber 辺局所化は明示入力で、完全関手の普遍性から推論しない。
使われ方：D2 の Perf lax pullback 比較と K-8 d8 の具体的入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：元の比較対角の始域を S に置く。方針：対象宇宙だけを上げる。
規約：対角の始域を選び直さない。使われ方：具体的 Verdier 列の左端。 -/
def dgOdotDiagonalSourceInput : PerfDGInput.{u, u + 1} R :=
  dgKUniverseInput.{u, u + 1, u + 1} R
    (DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source))

/-- 概要：元の実 gluing を S に置く。方針：同じ全 Hom を保持する。
規約：lax pullback 同定は未供給。使われ方：具体的 Verdier 列の中央。 -/
def dgOdotGluingInput : PerfDGInput.{u, u + 1} R :=
  dgKUniverseInput.{u, u + 1, u + 1} R (DGOdotGluing R d)

/-- 概要：元の比較対角を S の辺にする。方針：厳密 dg 関手を持ち上げる。
規約：比較対角の全 Hom を保つ。使われ方：β3 の包含の接続。 -/
def dgOdotDiagonalInputMap : dgOdotDiagonalSourceInput R d ⟶ dgOdotGluingInput R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1}
    (dgOdotQuotientInput R d).diagonal)

/-- 概要：元の実商射を S の辺にする。方針：同じ射影を持ち上げる。
規約：既存の商頂点を再利用する。使われ方：β3 の商射の接続。 -/
def dgOdotProjectionInputMap : dgOdotGluingInput R d ⟶ dgOdotQuotientInputVertex R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1}
    (dgOdotQuotientInput R d).projection)

/-- 概要：同じ包含の完全な ν 像。方針：固定界面の元の射を使う。
規約：一般の安定圏上の K は不要。使われ方：Sp の Verdier 条件。 -/
abbrev dgOdotDiagonalExactMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotDiagonalSourceInput R d))
    (dgKInputStableValue R (dgOdotGluingInput R d)) :=
  dgKInputNuMap R (dgOdotDiagonalInputMap R d)

/-- 概要：同じ実商射の完全な ν 像。方針：固定界面の元の射を使う。
規約：商の局所化性はまだ入力。使われ方：Sp の Verdier 条件。 -/
abbrev dgOdotProjectionExactMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotGluingInput R d))
    (dgKInputStableValue R (dgOdotQuotientInputVertex R d)) :=
  dgKInputNuMap R (dgOdotProjectionInputMap R d)

/-- 概要：β3 から同じ具体的二射へ供給する証拠。方針：Sp の三条件を分離する。
規約：未供給の核一致・全辺局所化を仮定から落とさない。
使われ方：具体的供給が届いたら各欄を差し替える接続口。 -/
structure DGOdotVerdierInput : Prop where
  fullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (dgOdotDiagonalExactMap R d).hom
  kernel (b : (dgKInputStableValue R (dgOdotGluingInput R d)).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((dgOdotProjectionExactMap R d).hom.app (Opposite.op ⦋0⦌) b) ↔
      b ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (dgOdotDiagonalExactMap R d)
  localization : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (dgOdotProjectionExactMap R d).hom
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (dgOdotDiagonalExactMap R d)))

namespace DGOdotVerdierInput
variable {R d} (h : DGOdotVerdierInput R d)
include h

/-- 概要：具体的な β3 証拠を Sp 正本の列条件へ接続する。
方針：同じ二射について三欄を渡す。規約：局所化 API を新設しない。
使われ方：K-8 d8 に渡す前の実商列。 -/
theorem isVerdier : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence (dgOdotDiagonalExactMap R d)
    (dgOdotProjectionExactMap R d) :=
  ⟨h.fullyFaithful, h.kernel, h.localization⟩

/-- 概要：元の三頂点と二射を持つ実列。方針：上の条件を束ねる。
規約：商を冪等完備化に置換しない。使われ方：ν 像の Verdier 提示。 -/
def sequence : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u + 1} where
  left := dgKInputStableValue R (dgOdotDiagonalSourceInput R d)
  middle := dgKInputStableValue R (dgOdotGluingInput R d)
  right := dgKInputStableValue R (dgOdotQuotientInputVertex R d)
  inclusion := dgOdotDiagonalExactMap R d
  projection := dgOdotProjectionExactMap R d
  isVerdier := h.isVerdier

end DGOdotVerdierInput
end SerrePositivity.KST.SConstruction
