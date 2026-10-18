module

public import SerrePositivity.KST.DerivedGeometry.LinearRepresentableCone
public import SerrePositivity.KST.DerivedGeometry.LinearComplexClosed
public import SerrePositivity.KST.DerivedGeometry.DGResolution.DerivedYoneda

/-!
# 具体的な後合成と実際の dg Yoneda の比較

概要：代表加群の具体的な後合成射を、既存 dg Yoneda の閉次数零の射と同定する。
方針：各評価の cochain を全次数の Yoneda 評価公式で計算する。
規約：有限 cell の cone に入る射を、別の関手へ置き換えずに比較する。
使われ方：Drinfeld §2.4、KST D4・§10-7 の前三角化の代表可能性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.KST.DerivedGeometry.LinearComplex

variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]

attribute [local instance] enrichment

variable [Small.{u} (CochainComplex C ℤ)]

/--
概要：dg Yoneda の閉次数零の射を評価すると具体的な後合成の chain map に一致する。
方針：単位からの閉 cochain を評価し、全次数の Yoneda の公式を適用する。
規約：通常の chain map と閉零射の既存の対応を使う。
使われ方：Drinfeld §2.4、KST D4 の代表加群の cone で使う射の比較。
-/
theorem yoneda_map_eval {X Y : CochainComplex C ℤ}
    (g : ForgetEnrichment.of (Complex A) X ⟶ ForgetEnrichment.of (Complex A) Y)
    (T : CochainComplex C ℤ) :
    (moduleEvaluation A (CochainComplex C ℤ) T).map
        ((dgYoneda A (CochainComplex C ℤ)).onClosed.map g) =
      mappingPostcompose A T (closedHomEquiv A X Y g) := by
  rw [moduleEvaluation_map]
  apply Cochain.ofHom_injective
  rw [complexClosedHomEquiv_cochain]
  change (cycleFromUnit _ ((g ≫ yonedaHom A (CochainComplex C ℤ) X Y) ≫
    moduleHomπ A (CochainComplex C ℤ) (representable A X) (representable A Y) T)).val = _
  rw [cycleFromUnit_postcomp, cycleFromUnit_postcomp]
  apply Cochain.ext₀
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change (((moduleHomπ A (CochainComplex C ℤ) (representable A X) (representable A Y) T).f 0
    ((yonedaHom A (CochainComplex C ℤ) X Y).f 0
      (cycleFromUnit (mappingComplex A X Y) g).val)).v q q (add_zero q)) h =
    h.comp (Cochain.ofHom (closedHomEquiv A X Y g)) (add_zero q)
  rw [yonedaHom_element]
  rw [forward_cochain, ← closedHomEquiv_cochain A X Y g]
  simp only [zero_mul, mul_zero, Int.negOnePow_zero, one_smul]

/--
概要：具体的な代表加群の後合成射と dg Yoneda の閉零射は同じ射。
方針：全評価で比較し、閉零射と chain map の往復を使う。
規約：cone の比較にはこの同じ射を使う。
使われ方：Drinfeld §2.4、KST D4・§10-7 の有限 cell の代表可能性。
-/
theorem representablePostcompose_eq_yoneda {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    representablePostcompose A f =
      (dgYoneda A (CochainComplex C ℤ)).onClosed.map ((closedHomEquiv A X Y).symm f) := by
  apply moduleMorphism_ext
  intro T
  rw [representablePostcompose_eval, yoneda_map_eval, Equiv.apply_symm_apply]

/--
概要：代表加群間の任意の射は、元の複体の chain map の後合成として表せる。
方針：全 Hom の Yoneda 同型から閉零の充満性を使う。
規約：導来圏の射にする前の、実際の dg 加群の射を扱う。
使われ方：Drinfeld §2.4、KST D4 の有限 cell の cone の代表可能性。
-/
theorem representableHom_lift {X Y : CochainComplex C ℤ}
    (g : ForgetEnrichment.of (Complex A) (representable A X) ⟶
      ForgetEnrichment.of (Complex A) (representable A Y)) :
    ∃ f : X ⟶ Y, representablePostcompose A f = g := by
  let : (dgYoneda A (CochainComplex C ℤ)).onClosed.Full :=
    (dgYoneda A (CochainComplex C ℤ)).onClosed_full_of_homIso
      (DGResolution.yoneda_hom_isIso A (CochainComplex C ℤ))
  obtain ⟨h, hh⟩ := (dgYoneda A (CochainComplex C ℤ)).onClosed.map_surjective g
  refine ⟨closedHomEquiv A X Y h, ?_⟩
  rw [representablePostcompose_eq_yoneda, Equiv.symm_apply_apply]
  exact hh

end SerrePositivity.KST.DerivedGeometry.LinearComplex
