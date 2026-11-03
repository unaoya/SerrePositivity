module

public import SerrePositivity.KST.DerivedGeometry.LinearComplexEnrichment
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
# 層にも使える複体 dg 圏の閉次数零

概要：一般の線形加法圏の複体 dg 圏の Z⁰ を実際の複体の圏と比較する。
方針：単位からの射と閉コチェインの対応を使い、単位と合成も照合する。
規約：dg 商の導来局所化との比較はこの Z⁰ 同値とは別。
使われ方：KST D4・§13 決定11、Toën Derived Azumaya §3.2 の層複体の dg 増強。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CochainComplex HomComplex MonoidalCategory
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.KST.DerivedGeometry.LinearComplex

attribute [local instance] enrichment

variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]

/--
概要：複体 dg 圏の閉次数零の射と通常の chain map の対応。
方針：単位からの射を閉コチェインへ移し、Mathlib の Cocycle.equivHom を使う。
規約：対象圏を加群の圏に限定しない。
使われ方：KST D4、Toën §3.2 の層の実際の複体との接続。
-/
def closedHomEquiv (X Y : CochainComplex C ℤ) :
    (ForgetEnrichment.of (Complex A) X ⟶ ForgetEnrichment.of (Complex A) Y) ≃ (X ⟶ Y) :=
  (unitCycleEquiv (mappingComplex A X Y)).trans
    { toFun c := Cocycle.homOf ⟨c.val, c.property⟩
      invFun f := ⟨Cochain.ofHom f, δ_ofHom f⟩
      left_inv c := by
        apply Subtype.ext
        exact Cocycle.cochain_ofHom_homOf_eq_coe ⟨c.val, c.property⟩
      right_inv f := Cocycle.homOf_ofHom_eq_self f }

/--
概要：閉射から得る chain map のコチェインは元の閉次数零の元。
方針：閉コチェインと chain map の往復の式を使う。
規約：単位からの射の評価を cycleFromUnit とする。
使われ方：KST D4、Toën §3.2 の比較関手の法則。
-/
lemma closedHomEquiv_cochain (X Y : CochainComplex C ℤ)
    (f : ForgetEnrichment.of (Complex A) X ⟶ ForgetEnrichment.of (Complex A) Y) :
    Cochain.ofHom (closedHomEquiv A X Y f) =
      (cycleFromUnit (mappingComplex A X Y) f).val :=
  Cocycle.cochain_ofHom_homOf_eq_coe _

/--
概要：閉次数零の単位は通常の恒等 chain map に対応する。
方針：恒等コチェインから作った単位の評価を計算する。
規約：元の複体の恒等射を保つ。
使われ方：KST D4、Toën §3.2 の Z⁰ 比較関手。
-/
lemma closedHomEquiv_id (X : CochainComplex C ℤ) :
    closedHomEquiv A X X (𝟙 (ForgetEnrichment.of (Complex A) X)) = 𝟙 X := by
  apply Cochain.ofHom_injective
  rw [closedHomEquiv_cochain]
  change (cycleFromUnit (mappingComplex A X X) (identity X)).val = _
  rw [identity, cycleFromUnit_unitFromCycle]

/--
概要：閉次数零の合成は通常の chain map の合成に対応する。
方針：単位からの射のテンソルと豊穣合成の次数零の値を計算する。
規約：次数零では Koszul 符号は 1。
使われ方：KST D4、Toën §3.2 の Z⁰ 比較関手。
-/
lemma closedHomEquiv_comp (X Y Z : CochainComplex C ℤ)
    (f : ForgetEnrichment.of (Complex A) X ⟶ ForgetEnrichment.of (Complex A) Y)
    (g : ForgetEnrichment.of (Complex A) Y ⟶ ForgetEnrichment.of (Complex A) Z) :
    closedHomEquiv A X Z (f ≫ g) = closedHomEquiv A X Y f ≫ closedHomEquiv A Y Z g := by
  apply Cochain.ofHom_injective
  rw [closedHomEquiv_cochain, Cochain.ofHom_comp,
    closedHomEquiv_cochain, closedHomEquiv_cochain]
  change (cycleFromUnit (mappingComplex A X Z)
    (((λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ g)) ≫ forwardComposition X Y Z)).val = _
  rw [cycleFromUnit_postcomp]
  change (forwardComposition X Y Z).f 0
    ((((λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ g)).f 0) (1 : A)) = _
  rw [unit_tensor_apply]
  change (forwardComposition X Y Z).f 0
    (HomologicalComplex.ιTensorObj (mappingComplex A X Y) (mappingComplex A Y Z) 0 0 0 rfl
      ((cycleFromUnit (mappingComplex A X Y) f).val ⊗ₜ[A]
        (cycleFromUnit (mappingComplex A Y Z) g).val)) = _
  rw [forwardComposition_apply]
  simp

/--
概要：複体 dg 圏の Z⁰ から通常の複体の圏への比較関手。
方針：射の閉コチェイン対応を単位・合成の法則と束ねる。
規約：対象は元の複体を取る。
使われ方：KST D4、Toën §3.2 の層複体の比較。
-/
def closedToComplex : ClosedCategory A (CochainComplex C ℤ) ⥤ CochainComplex C ℤ where
  obj X := ForgetEnrichment.to (Complex A) X
  map f := closedHomEquiv A _ _ f
  map_id X := closedHomEquiv_id A X
  map_comp f g := closedHomEquiv_comp A _ _ _ f g

/--
概要：閉次数零の比較は忠実。
方針：各 Hom の対応の単射性を使う。
規約：通常の chain map の等式を反映する。
使われ方：KST D4、Toën §3.2 の Z⁰ 同値。
-/
instance closedToComplex_faithful : (closedToComplex (C := C) A).Faithful where
  map_injective h := (closedHomEquiv A _ _).injective h

/--
概要：閉次数零の比較は充満。
方針：各 chain map に対応する閉コチェインを取る。
規約：選択した射の逆対応は明示的な同値から得る。
使われ方：KST D4、Toën §3.2 の Z⁰ 同値。
-/
instance closedToComplex_full : (closedToComplex (C := C) A).Full where
  map_surjective := (closedHomEquiv A _ _).surjective

/--
概要：閉次数零の比較は本質的全射。
方針：各複体をそのまま dg 圏の対象へ戻す。
規約：対象の追加の解消は不要。
使われ方：KST D4、Toën §3.2 の Z⁰ 同値。
-/
instance closedToComplex_essSurj : (closedToComplex (C := C) A).EssSurj where
  mem_essImage X := ⟨ForgetEnrichment.of (Complex A) X, ⟨Iso.refl _⟩⟩

/--
概要：複体 dg 圏の閉次数零の比較は圏同値。
方針：忠実・充満・本質的全射をまとめる。
規約：H⁰ や導来圏との同値とは区別する。
使われ方：KST D4・§13 決定11、Toën §3.2 の層複体の増強。
-/
instance closedToComplex_isEquivalence : (closedToComplex (C := C) A).IsEquivalence where

end SerrePositivity.KST.DerivedGeometry.LinearComplex
