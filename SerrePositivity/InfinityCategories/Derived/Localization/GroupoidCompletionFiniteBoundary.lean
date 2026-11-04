module

public import SerrePositivity.InfinityCategories.Derived.Localization.GroupoidCompletionFiniteFactorization
public import SerrePositivity.InfinityCategories.Derived.FiniteMappingCylinder
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering

/-!
概要：元の亜群化の有限全族・指定境界族・指定境界 Homotopy を同じ有限台へ下ろす。
方針：元の境界円柱を有限写像円柱上の一射へ貼り、一つの全因子化同型を制限する。
規約：有限台と全比較は一つを共有し、境界比較を点ごとに選び直さない。
使われ方：c5 の任意の完成側有限境界と比較円柱の同時処理。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.F2
namespace SerrePositivity.KST.LocalizingInvariants

variable {L K X : SSet.{u}} (j : L ⟶ K) (f : K ⟶ groupoidCompletion X)
  {a : L ⟶ groupoidCompletion X} (H : SSet.Homotopy a (j ≫ f))

/-- 指定された元の境界 Homotopy と全族を貼った一つの全写像。 -/
def completedBoundaryCylinderMap : finiteMappingCylinder j ⟶ groupoidCompletion X :=
  pushout.desc ((β_ (Δ[1] : SSet.{u}) L).hom ≫ H.h) f (by
    rw [← Category.assoc, prismEndpoint_one_braiding]
    exact H.h₁)

lemma completedBoundaryCylinderMap_family :
    pushout.inr (prismEndpoint 1 L) j ≫ completedBoundaryCylinderMap j f H = f :=
  pushout.inr_desc _ _ _

lemma completedBoundaryCylinderMap_boundary :
    finiteMappingCylinderSource j ≫ completedBoundaryCylinderMap j f H = a := by
  rw [finiteMappingCylinderSource, Category.assoc, completedBoundaryCylinderMap,
    pushout.inl_desc, ← Category.assoc, prismEndpoint_zero_braiding]
  exact H.h₀

lemma completedBoundaryCylinderMap_prism :
    (finiteMappingCylinderHomotopy j).h ≫ completedBoundaryCylinderMap j f H = H.h := by
  change ((β_ L (Δ[1] : SSet.{u})).hom ≫ pushout.inl _ _) ≫ _ = _
  rw [Category.assoc, completedBoundaryCylinderMap, pushout.inl_desc,
    ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- 有限な元の境界円柱全体を、一つの元の有限部分複体の完成へ移したデータ。 -/
structure GroupoidCompletionFiniteBoundary where
  support : FiniteSubcomplex X
  whole : finiteMappingCylinder j ⟶ groupoidCompletion support.val
  comparison : FunctorIso (whole ≫ groupoidCompletionMapOf support.val.ι)
    (completedBoundaryCylinderMap j f H)

/-- 任意の有限境界・全族・境界比較を、同じ一つの有限台と全同型で同時に回収する。 -/
lemma exists_groupoidCompletionFiniteBoundary [L.Finite] [K.Finite] :
    Nonempty (GroupoidCompletionFiniteBoundary j f H) := by
  obtain ⟨A, b, ⟨e⟩⟩ := groupoidCompletion_finite_factorization
    (completedBoundaryCylinderMap j f H)
  exact ⟨⟨A, b, e⟩⟩

namespace GroupoidCompletionFiniteBoundary
variable {j f H} (d : GroupoidCompletionFiniteBoundary j f H)

def family : K ⟶ groupoidCompletion d.support.val :=
  pushout.inr (prismEndpoint 1 L) j ≫ d.whole

def boundary : L ⟶ groupoidCompletion d.support.val :=
  finiteMappingCylinderSource j ≫ d.whole

/-- 同じ有限台上の、指定境界から全族の制限への実 Homotopy。 -/
def boundaryHomotopy : SSet.Homotopy d.boundary (j ≫ d.family) := by
  let V := functorHomotopyPostcomp (finiteMappingCylinderHomotopy j) d.whole
  exact { h := V.h, h₀ := V.h₀, h₁ := V.h₁.trans (Category.assoc _ _ _), rel := V.rel }

/-- 同じ一つの全比較の K 制限。 -/
def familyIso : FunctorIso (d.family ≫ groupoidCompletionMapOf d.support.val.ι) f := by
  have e := FunctorIso.precomp d.comparison (pushout.inr (prismEndpoint 1 L) j)
  simpa only [family, Category.assoc, completedBoundaryCylinderMap_family] using e

/-- 同じ一つの全比較の L 始端制限。 -/
def boundaryIso : FunctorIso (d.boundary ≫ groupoidCompletionMapOf d.support.val.ι) a := by
  have e := FunctorIso.precomp d.comparison (finiteMappingCylinderSource j)
  simpa only [boundary, Category.assoc, completedBoundaryCylinderMap_boundary] using e

/-- 同じ一つの全比較の全境界円柱制限。 -/
def boundaryPrismIso : FunctorIso
    (d.boundaryHomotopy.h ≫ groupoidCompletionMapOf d.support.val.ι) H.h := by
  have e := FunctorIso.precomp d.comparison (finiteMappingCylinderHomotopy j).h
  simpa only [boundaryHomotopy, functorHomotopyPostcomp, Category.assoc,
    completedBoundaryCylinderMap_prism] using e

end GroupoidCompletionFiniteBoundary
end SerrePositivity.KST.LocalizingInvariants
