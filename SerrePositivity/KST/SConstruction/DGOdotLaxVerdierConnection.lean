module
public import SerrePositivity.KST.SConstruction.DGOdotVerdierInput
public import SerrePositivity.KST.SConstruction.DGOdotTargetInputTriangle

/-!
概要：同じ dg 四角形の Perf gluing 比較から K-8 d8 の実二射を固定する。
方針：D2 の比較同値と元の商射の整合を入力し、包含の充満忠実性を合成する。
規約：比較先の核一致と局所化は未供給の明示入力。輸送の一般 API を新設しない。
使われ方：具体的供給を差し替えられる、固定 S・ν の Verdier 接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：元の左代数を S に置く。方針：右代数と同じ宇宙を使う。
規約：実代数を置換しない。使われ方：元の lax pullback の左入力。 -/
def dgOdotLeftInput : PerfDGInput.{u, u + 1} R :=
  dgKUniverseInput.{u, 0, u + 1} R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left)

/-- 概要：元の下辺代数射を S に置く。方針：同じ dg 射を持ち上げる。
規約：元の角入力を保持する。使われ方：lax pullback の第一脚。 -/
def dgOdotLowerInputMap : dgOdotLeftInput R d ⟶ dgOdotCornerInput R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, 0, 0, u + 1, u + 1} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower))

/-- 概要：同じ元の二脚の完全な ν 像。方針：固定界面を使う。
規約：別の脚を選ばない。使われ方：D2 比較の標的。 -/
abbrev dgOdotLowerExactMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotLeftInput R d))
    (dgKInputStableValue R (dgOdotCornerInput R d)) :=
  dgKInputNuMap R (dgOdotLowerInputMap R d)

/-- 概要：元の右脚の完全な ν 像。方針：既存の上辺入力を使う。
規約：元の右代数射を保つ。使われ方：D2 比較の第二脚。 -/
abbrev dgOdotUpperExactMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotRightInput R d))
    (dgKInputStableValue R (dgOdotCornerInput R d)) :=
  dgKInputNuMap R (dgOdotUpperInputMap R d)

/-- 概要：元の二脚に対する実 Perf lax pullback。方針：Sp 正本を特殊化する。
規約：dg gluing との同定は入力に残す。使われ方：d8 の中央圏。 -/
abbrev dgOdotPerfLaxCategory : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u + 1} :=
  laxCategory (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)

/-- 概要：D2 と β3 の未供給比較を隔離する。方針：同じ二射と整合式を保持する。
規約：核一致・局所化の輸送も明示入力。使われ方：具体的供給後の差し替え口。 -/
structure DGOdotLaxVerdierInput where
  source : DGOdotVerdierInput R d
  comparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R (dgOdotGluingInput R d))
    (dgOdotPerfLaxCategory R d)
  isEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence comparison.hom
  projection : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgOdotPerfLaxCategory R d)
    (dgKInputStableValue R (dgOdotQuotientInputVertex R d))
  projection_iso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (comparison.hom ≫ projection.hom)
    (dgOdotProjectionExactMap R d).hom
  kernel (b : (dgOdotPerfLaxCategory R d).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (projection.hom.app (Opposite.op ⦋0⦌) b) ↔
      b ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap _ _ from
        ⟨(dgOdotDiagonalExactMap R d).hom ≫ comparison.hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _⟩)
  localization : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization projection.hom
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap _ _ from
        ⟨(dgOdotDiagonalExactMap R d).hom ≫ comparison.hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _⟩)))

namespace DGOdotLaxVerdierInput
variable {R d} (h : DGOdotLaxVerdierInput R d)

/-- 概要：元の対角と D2 比較の合成。方針：同じ完全射を合成する。
規約：包含を選び直さない。使われ方：d8 の左射。 -/
def inclusion : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R (dgOdotDiagonalSourceInput R d))
    (dgOdotPerfLaxCategory R d) :=
  ⟨(dgOdotDiagonalExactMap R d).hom ≫ h.comparison.hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _⟩

/-- 概要：包含の充満忠実性を保持する。方針：β3 と D2 の同値を合成する。
規約：核一致から推論しない。使われ方：Sp の列条件。 -/
lemma inclusion_fullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful h.inclusion.hom :=
  h.source.fullyFaithful.comp h.isEquivalence.isFullyFaithful

/-- 概要：明示された具体的証拠から d8 の列条件を満たす。
方針：導いた充満忠実性と未供給の二条件を Sp 正本へ渡す。
規約：D2・β3 の無条件完成ではない。使われ方：既存の K-8 d8。 -/
theorem isVerdier : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence h.inclusion h.projection :=
  ⟨h.inclusion_fullyFaithful, h.kernel, h.localization⟩

/-- 概要：元の商射は D2 比較と同じ射の合成で回収される。
方針：指定された整合式を保持する。規約：ホモトピー圏だけへ落とさない。
使われ方：元の二射の照合。 -/
def projection_original : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (h.comparison.hom ≫ h.projection.hom)
    (dgOdotProjectionExactMap R d).hom := h.projection_iso

/-- 概要：包含後の商合成は元の対角後の商合成を回収する。
方針：同じ射の結合則と指定関手同型を使う。規約：S 内零化を結論しない。
使われ方：Sp-6 の零化入力を接続する境界。 -/
def composite_original : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (h.inclusion.hom ≫ h.projection.hom)
    ((dgOdotDiagonalExactMap R d).hom ≫ (dgOdotProjectionExactMap R d).hom) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (((dgOdotDiagonalExactMap R d).hom ≫ h.comparison.hom) ≫
    h.projection.hom) _
  rw [Category.assoc]
  exact h.projection_iso.precomp (dgOdotDiagonalExactMap R d).hom

end DGOdotLaxVerdierInput
end SerrePositivity.KST.SConstruction
