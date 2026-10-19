module
public import SerrePositivity.InfinityCategories.Derived.CellDGResolutionNerve
public import SerrePositivity.InfinityCategories.Derived.DGQuotientZeroObjects
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFlatness

/-! # 平坦分解を先行させた dg 商の nerve

概要：具体的な cell 分解後の path 商を取り、元の nerve から ∞ 関手を構成する。
方針：実際に構成した増大の nerve の逆と商包含を合成し、屋根との可逆二胞体を保持する。
規約：元の Hom の K-flat 性を要求しない。使われ方：β3 の導来 dg 商の模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 具体的分解における指定対象集合の逆像。 -/
def resolvedDGNullObjects (P : Set D) : Set (DGCategoryCellResolution.Source A D) :=
  fun x => (DGCategoryCellResolution.augmentation A D).obj x ∈ P

/-- 平坦分解後の指定対象は、元の対象ラベルの同じ条件を満たすもの。 -/
lemma resolvedDGNullObjects_mem (P : Set D) (x : D) :
    (⟨x⟩ : DGCategoryCellResolution.Source A D) ∈ resolvedDGNullObjects A D P ↔ x ∈ P := Iff.rfl

/-- 平坦分解後の商の dg nerve。 -/
abbrev resolvedDGQuotientNerve (P : Set D) :=
  dgQuotientNerve A (DGCategoryCellResolution.Source A D) (resolvedDGNullObjects A D P)

/-- 分解の nerve から商の nerve への実際の射影。 -/
def resolvedDGQuotientProjection (P : Set D) :
    dgNerve A (DGCategoryCellResolution.Source A D) ⟶ resolvedDGQuotientNerve A D P :=
  dgQuotientNerveProjection A (DGCategoryCellResolution.Source A D) (resolvedDGNullObjects A D P)

/-- 分解の ∞ 圏同値の逆を通る、元の nerve から平坦商への関手。 -/
def resolvedDGQuotientFunctor (P : Set D) : dgNerve A D ⟶ resolvedDGQuotientNerve A D P :=
  (dgCellResolutionNerveEquivalence A D).inv ≫ resolvedDGQuotientProjection A D P

/-- 元からの関手は、分解上で実際の商射影と可逆二胞体で一致する。 -/
def resolvedDGQuotientRoofIso (P : Set D) :
    FunctorIso (dgNerve.map (DGCategoryCellResolution.augmentation A D) ≫
      resolvedDGQuotientFunctor A D P) (resolvedDGQuotientProjection A D P) := by
  change FunctorIso ((dgCellResolutionNerveEquivalence A D).hom ≫
    ((dgCellResolutionNerveEquivalence A D).inv ≫ resolvedDGQuotientProjection A D P)) _
  simpa only [Category.assoc, Category.id_comp] using
    ((dgCellResolutionNerveEquivalence A D).homInvIso.postcomp (resolvedDGQuotientProjection A D P))

/-- 分解後の path 商には、証明済みの一方向 K-flat 条件を渡せる。 -/
lemma resolvedDGQuotient_localKFlat (P : Set D) :
    DGQuotient.localKFlat A (DGCategoryCellResolution.Source A D) (resolvedDGNullObjects A D P) :=
  DGQuotient.allHomKFlat_local A _ (DGCategoryCellResolution.source_homKFlat A D) _

end SerrePositivity.InfinityCategories
