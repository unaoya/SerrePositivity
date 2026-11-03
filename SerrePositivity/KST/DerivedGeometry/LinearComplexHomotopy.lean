module

public import SerrePositivity.KST.DerivedGeometry.LinearComplexClosed
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# 複体 dg 圏の H⁰ と通常のホモトピー圏

概要：一般の線形加法圏の複体 dg 圏の H⁰ を Mathlib のホモトピー圏と同定する。
方針：dg の境界関係を通常の鎖ホモトピーと照合する。
規約：acyclic 商の H⁰ と導来圏との比較は後続の別定理。
使われ方：KST D4・§13 決定11、Toën Derived Azumaya §3.2 の層複体の増強。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.KST.DerivedGeometry.LinearComplex

attribute [local instance] enrichment

variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]

/--
概要：複体 dg 圏の境界関係は通常の鎖ホモトピーに一致する。
方針：単位からの射の境界式を Mathlib の equivHomotopy へ渡す。
規約：ホモトピーの次数は -1。
使われ方：KST D4、Toën §3.2 の H⁰ 比較。
-/
lemma boundary_iff (X Y : CochainComplex C ℤ)
    (f g : ForgetEnrichment.of (Complex A) X ⟶ ForgetEnrichment.of (Complex A) Y) :
    boundaryRelation A (CochainComplex C ℤ) f g ↔
      Nonempty (Homotopy (closedHomEquiv A X Y f) (closedHomEquiv A X Y g)) := by
  rw [boundaryRelation, unit_homotopy_boundary]
  constructor
  · rintro ⟨h, dh⟩
    apply Nonempty.intro
    refine (Cochain.equivHomotopy _ _).symm ⟨h, ?_⟩
    rw [closedHomEquiv_cochain, closedHomEquiv_cochain]
    change _ = (mappingComplex A X Y).d (-1) 0 h + _
    change (mappingComplex A X Y).d (-1) 0 h =
      (cycleFromUnit (mappingComplex A X Y) f).val -
        (cycleFromUnit (mappingComplex A X Y) g).val at dh
    rw [dh]
    abel
  · rintro ⟨h⟩
    refine ⟨Cochain.ofHomotopy h, ?_⟩
    change δ (-1) 0 (Cochain.ofHomotopy h) = _
    rw [δ_ofHomotopy, closedHomEquiv_cochain, closedHomEquiv_cochain]
    rfl

/--
概要：複体 dg 圏の H⁰ から通常のホモトピー圏への比較関手。
方針：Z⁰ の比較とホモトピー商の関手を境界関係に沿って降下する。
規約：対象は実際の非有界複体を保つ。
使われ方：KST D4、Toën §3.2 の層のホモトピー圏への接続。
-/
def homotopyComparison :
    SerrePositivity.DifferentialGraded.HomotopyCategory A (CochainComplex C ℤ) ⥤
      _root_.HomotopyCategory C (.up ℤ) :=
  CategoryTheory.Quotient.lift _
    (closedToComplex A ⋙ _root_.HomotopyCategory.quotient C (.up ℤ))
    (by
      intro X Y f g h
      exact _root_.HomotopyCategory.eq_of_homotopy _ _ ((boundary_iff A X Y f g).mp h).some)

/--
概要：H⁰ 比較は元の Z⁰ 比較とホモトピー商関手の合成から得られる。
方針：商関手の降下の仕様を使う。
規約：実際の比較関手の四角形を等式で固定する。
使われ方：KST D4、Toën §3.2 の局所化との比較。
-/
lemma homotopyComparison_fac :
    toHomotopy A (CochainComplex C ℤ) ⋙ homotopyComparison A =
      closedToComplex A ⋙ _root_.HomotopyCategory.quotient C (.up ℤ) :=
  CategoryTheory.Quotient.lift_spec _ _ _

/--
概要：H⁰ 比較は充満。
方針：通常のホモトピー圏の射を chain map に、次に閉次数零の射へ持ち上げる。
規約：既存の二つの充満な商・比較を使う。
使われ方：KST D4、Toën §3.2 の H⁰ 同値。
-/
instance homotopyComparison_full : (homotopyComparison (C := C) A).Full where
  map_surjective {X Y} f := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨g, rfl⟩ := (_root_.HomotopyCategory.quotient C (.up ℤ)).map_surjective f
    obtain ⟨h, rfl⟩ := (closedToComplex A).map_surjective g
    exact ⟨(toHomotopy A (CochainComplex C ℤ)).map h, rfl⟩

/--
概要：H⁰ 比較は忠実。
方針：通常のホモトピー圏での等式を鎖ホモトピーへ戻し、境界関係へ移す。
規約：一般の線形加法圏の複体での主張。
使われ方：KST D4、Toën §3.2 の H⁰ 同値。
-/
instance homotopyComparison_faithful : (homotopyComparison (C := C) A).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨f, rfl⟩ := (toHomotopy A (CochainComplex C ℤ)).map_surjective f
    obtain ⟨g, rfl⟩ := (toHomotopy A (CochainComplex C ℤ)).map_surjective g
    have hh := _root_.HomotopyCategory.homotopyOfEq
      ((closedToComplex A).map f) ((closedToComplex A).map g) h
    exact (toHomotopy_map_eq_iff A (CochainComplex C ℤ) f g).mpr
      ((boundary_iff A _ _ f g).mpr ⟨hh⟩)

/--
概要：H⁰ 比較は本質的全射。
方針：各複体を同じ対象として閉次数零の商へ送る。
規約：対象の解消や有界性を仮定しない。
使われ方：KST D4、Toën §3.2 の H⁰ 同値。
-/
instance homotopyComparison_essSurj : (homotopyComparison (C := C) A).EssSurj where
  mem_essImage X :=
    ⟨(toHomotopy A (CochainComplex C ℤ)).obj
      (ForgetEnrichment.of (Complex A) X.as), ⟨Iso.refl _⟩⟩

/--
概要：複体 dg 圏の H⁰ 比較は圏同値。
方針：充満・忠実・本質的全射をまとめる。
規約：acyclic の dg 商はまだここで取らない。
使われ方：KST D4・§13 決定11、Toën §3.2 の dg 増強の検証。
-/
instance homotopyComparison_isEquivalence : (homotopyComparison (C := C) A).IsEquivalence where

end SerrePositivity.KST.DerivedGeometry.LinearComplex
