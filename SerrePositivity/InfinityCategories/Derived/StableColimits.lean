module
public import SerrePositivity.InfinityCategories.Derived.ComplexSpanPresentation
public import SerrePositivity.InfinityCategories.Derived.SemifreeColimits
public import SerrePositivity.InfinityCategories.Derived.StableLimits

/-! # 導来 ∞ 圏の全 span の余極限と cofiber

概要：任意の span に対する標準 cofiber 押し出しを作り、全辺の cofiber を構成する。
方針：全複体への充満包含で span を表示し、Semifree 内の標準 cofiber を元の図式へ戻す。
規約：IsStable を仮定しない。使われ方：D7 の cofiber_exists。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet DGNerve
open scoped Simplicial
variable {S : Type u} [CommRing S]

/-- D(S) の span の鎖写像による表示。 -/
abbrev derivedSpanPresentation
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    ComplexSpanPresentation (p ≫ derivedInfinityInclusion) :=
  presentComplexSpan (p ≫ derivedInfinityInclusion)

/-- 表示の始域は semifree。 -/
lemma derivedSpanPresentation_source
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    complexSemifree S (derivedSpanPresentation p).sourceObj := by
  let s : Simplex S (Semifree S) 1 := SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ p)
  exact (s.obj 0).property

/-- 表示の左終域は semifree。 -/
lemma derivedSpanPresentation_left
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    complexSemifree S (derivedSpanPresentation p).leftObj := by
  let s : Simplex S (Semifree S) 1 := SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ p)
  exact (s.obj 1).property

/-- 表示の右終域は semifree。 -/
lemma derivedSpanPresentation_right
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    complexSemifree S (derivedSpanPresentation p).rightObj := by
  let s : Simplex S (Semifree S) 1 := SSet.yonedaEquiv (horn₂₀.ι₀₂ ≫ p)
  exact (s.obj 1).property

/-- 任意の span の標準 cofiber 正方形を D(S) 内で構成する。 -/
def derivedSpanCofiberSquare
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S :=
  semifreeCofiberSquare (derivedSpanPresentation p).leftMap (derivedSpanPresentation p).rightMap
    (derivedSpanPresentation_source p) (derivedSpanPresentation_left p)
    (derivedSpanPresentation_right p)

/-- 任意の span の標準 cofiber 正方形は ∞ 押し出し。 -/
lemma derivedSpanCofiberSquare_isPushout
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    IsPushoutSquare (derivedSpanCofiberSquare p) := semifreeCofiberSquare_isPushout _ _ _ _ _

/-- 構成した正方形の span は指定された元の図式に厳密に等しい。 -/
lemma derivedSpanCofiberSquare_span
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    pushoutSpan (derivedSpanCofiberSquare p) = p := by
  apply (cancel_mono (derivedInfinityInclusion (S := S))).1
  change pushoutSpan (derivedSpanCofiberSquare p ≫ derivedInfinityInclusion) =
    p ≫ derivedInfinityInclusion
  rw [derivedSpanCofiberSquare, semifreeCofiberSquare_inclusion]
  exact (derivedSpanPresentation p).span_eq

/-- D(S) の任意の span は余極限を持つ。 -/
lemma derivedInfinityCategory_hasColimit_span
    (p : (horn 2 0 : SSet.{u + 1}) ⟶ derivedInfinityCategory S) : HasColimit p := by
  have h : HasColimit (pushoutSpan (derivedSpanCofiberSquare p)) :=
    ⟨pushoutCocone (derivedSpanCofiberSquare p), derivedSpanCofiberSquare_isPushout p⟩
  rwa [derivedSpanCofiberSquare_span] at h

/-- D(S) の全ての指定された辺は cofiber 正方形を持つ。 -/
lemma derivedInfinityCategory_cofiber_exists {x y : (derivedInfinityCategory S) _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj (derivedInfinityCategory S)) x y) :
    Nonempty (CofiberSquare f) :=
  exists_cofiberSquare_of_span_colimits derivedInfinityCategory_hasColimit_span f

end SerrePositivity.InfinityCategories
