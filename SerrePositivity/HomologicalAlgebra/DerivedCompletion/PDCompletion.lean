module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Pair.Iteration
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Complete

/-! # 導来(p,d)完備化の実際のH⁰と環としての普遍性

BS共通要求F3の公開入口。任意の可換環を対象とし、p正則性・Noether性・
ねじれの有界性・古典的完備性を追加しない。一般の有限座標への拡張やδ構造の延長は別工程。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 元の(p,d)の冪のKoszul塔のホモトピー逆極限による複体。 -/
abbrev pdCompletionComplex (p : ℕ) (d : R) :=
  koszulCompletionComplex R (pairKoszulCoordinates R (p : R) d)

/-- 実際の複体を標準導来圏へ移した完備化対象。 -/
abbrev pdCompletionObject (p : ℕ) (d : R) :=
  koszulCompletionObject R (pairKoszulCoordinates R (p : R) d)

/-- 実際の(p,d)完備化複体の零次ホモロジー。 -/
abbrev PDCompletionH0 (p : ℕ) (d : R) := PairCompletionH0 R (p : R) d

/-- 実際のH⁰の可換環構造。 -/
@[instance_reducible] def pdCompletionCommRing (p : ℕ) (d : R) : CommRing (PDCompletionH0 R p d) :=
  pairCompletionCommRing R (p : R) d

/-- 実際のH⁰の元のR作用と両立する代数構造。 -/
@[instance_reducible] def pdCompletionAlgebra (p : ℕ) (d : R) :
    letI := pdCompletionCommRing R p d; Algebra R (PDCompletionH0 R p d) :=
  pairCompletionAlgebra R (p : R) d

/-- 元の環から実際のH⁰への標準環準同型。 -/
def pdCompletionUnit (p : ℕ) (d : R) :
    letI := pdCompletionCommRing R p d; R →+* PDCompletionH0 R p d :=
  pairCompletionUnitRingHom R (p : R) d

/-- 公開した標準環準同型は、元のKoszul複体の標準写像に誘導されたH⁰写像そのもの。 -/
theorem pdCompletionUnit_apply (p : ℕ) (d r : R) :
    pdCompletionUnit R p d r = koszulCompletionH0Unit R (pairKoszulCoordinates R (p : R) d) r :=
  pairCompletionUnitRingHom_apply R (p : R) d r

/-- 完備化の実導来対象はp導来完備。 -/
theorem pdCompletionObject_isComplete_p (p : ℕ) (d : R) :
    IsComplete R (p : R) (pdCompletionObject R p d) := by
  simpa only [pdCompletionObject, pairKoszulCoordinates, Fin.snoc_apply_zero] using
    koszulCompletionObject_isComplete R (pairKoszulCoordinates R (p : R) d) 0

/-- 完備化の実導来対象はd導来完備。 -/
theorem pdCompletionObject_isComplete_d (p : ℕ) (d : R) :
    IsComplete R d (pdCompletionObject R p d) := by
  simpa only [pdCompletionObject, pairKoszulCoordinates, Fin.snoc_last] using
    koszulCompletionObject_isComplete R (pairKoszulCoordinates R (p : R) d) (Fin.last 1)

/-- 標準環準同型から得るR作用の下で、H⁰はp導来完備。 -/
theorem pdCompletionH0_isComplete_p (p : ℕ) (d : R) :
    letI := pdCompletionCommRing R p d
    IsModuleComplete R (p : R) (@ModuleCat.of R _ (PDCompletionH0 R p d) _
      (@Algebra.toModule R (PDCompletionH0 R p d) _ _ (pdCompletionUnit R p d).toAlgebra)) :=
  pairCompletion_isModuleComplete_unit_first R (p : R) d

/-- 標準環準同型から得るR作用の下で、H⁰はd導来完備。 -/
theorem pdCompletionH0_isComplete_d (p : ℕ) (d : R) :
    letI := pdCompletionCommRing R p d
    IsModuleComplete R d (@ModuleCat.of R _ (PDCompletionH0 R p d) _
      (@Algebra.toModule R (PDCompletionH0 R p d) _ _ (pdCompletionUnit R p d).toAlgebra)) :=
  pairCompletion_isModuleComplete_unit_second R (p : R) d

/-- 両座標に導来完備な離散環への任意の準同型は、実際のH⁰から一意に延長する。 -/
theorem pdCompletion_existsUnique_ringHom (p : ℕ) (d : R)
    (T : Type u) [CommRing T] (g : R →+* T)
    (hp : letI := g.toAlgebra; IsModuleComplete R (p : R) (ModuleCat.of R T))
    (hd : letI := g.toAlgebra; IsModuleComplete R d (ModuleCat.of R T)) :
    letI := pdCompletionCommRing R p d
    ∃! h : PDCompletionH0 R p d →+* T, h.comp (pdCompletionUnit R p d) = g :=
  pairCompletion_existsUnique_ringHom R (p : R) d T g hp hd

/-- 実際の(p,d)のH⁰と一座標の反復の、標準写像を保つ環同型。 -/
def pdCompletionIteratedEquiv (p : ℕ) (d : R) :
    letI := pdCompletionCommRing R p d
    letI := iteratedCompletionCommRing R (p : R) d
    PDCompletionH0 R p d ≃+* IteratedCompletionH0 R (p : R) d :=
  pairCompletionIteratedEquiv R (p : R) d

/-- 反復との比較同型の標準写像の図式。 -/
theorem pdCompletionIteratedEquiv_unit (p : ℕ) (d r : R) :
    pdCompletionIteratedEquiv R p d (pdCompletionUnit R p d r) =
      iteratedCompletionUnitRingHom R (p : R) d r :=
  pairCompletionIteratedEquiv_unit R (p : R) d r

end SerrePositivity.DerivedCompletion
