module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.ComplexSpanPresentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.SemifreeColimits
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.StableLimits

/-! # 導来 ∞ 圏の全 span の余極限と cofiber

概要：任意の span に対する標準 cofiber 押し出しを作り、全辺の cofiber を構成する。
方針：全複体への充満包含で span を表示し、Semifree 内の標準 cofiber を元の図式へ戻す。
規約：IsStable を仮定しない。使われ方：D7 の cofiber_exists。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]

/-- D(S) の span の鎖写像による表示。 -/
abbrev derivedSpanPresentation
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSpanPresentation (p ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.presentComplexSpan (p ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)

/-- 表示の始域は semifree。 -/
lemma derivedSpanPresentation_source
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (derivedSpanPresentation p).sourceObj := by
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) 1 := SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ p)
  exact (s.obj 0).property

/-- 表示の左終域は semifree。 -/
lemma derivedSpanPresentation_left
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (derivedSpanPresentation p).leftObj := by
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) 1 := SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ p)
  exact (s.obj 1).property

/-- 表示の右終域は semifree。 -/
lemma derivedSpanPresentation_right
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (derivedSpanPresentation p).rightObj := by
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) 1 := SSet.yonedaEquiv (horn₂₀.ι₀₂ ≫ p)
  exact (s.obj 1).property

/-- 任意の span の標準 cofiber 正方形を D(S) 内で構成する。 -/
def derivedSpanCofiberSquare
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSquare (derivedSpanPresentation p).leftMap (derivedSpanPresentation p).rightMap
    (derivedSpanPresentation_source p) (derivedSpanPresentation_left p)
    (derivedSpanPresentation_right p)

/-- 任意の span の標準 cofiber 正方形は ∞ 押し出し。 -/
lemma derivedSpanCofiberSquare_isPushout
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (derivedSpanCofiberSquare p) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSquare_isPushout _ _ _ _ _

/-- 構成した正方形の span は指定された元の図式に厳密に等しい。 -/
lemma derivedSpanCofiberSquare_span
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (derivedSpanCofiberSquare p) = p := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion (S := S))).1
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (derivedSpanCofiberSquare p ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion) =
    p ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion
  rw [derivedSpanCofiberSquare, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSquare_inclusion]
  exact (derivedSpanPresentation p).span_eq

/-- D(S) の任意の span は余極限を持つ。 -/
lemma derivedInfinityCategory_hasColimit_span
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (derivedSpanCofiberSquare p)) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (derivedSpanCofiberSquare p), derivedSpanCofiberSquare_isPushout p⟩
  rwa [derivedSpanCofiberSquare_span] at h

/-- D(S) の全ての指定された辺は cofiber 正方形を持つ。 -/
lemma derivedInfinityCategory_cofiber_exists {x y : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)) x y) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_cofiberSquare_of_span_colimits derivedInfinityCategory_hasColimit_span f

end SerrePositivity.InfinityCategories.Project.DerivedCategories
