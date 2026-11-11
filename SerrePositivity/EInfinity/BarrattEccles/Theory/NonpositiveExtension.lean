module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# 非正次数の複体の制限と延長

## 概要
HA 3.2.4.7 の二色の係数比較を、鎖次数から元の整数コチェイン次数へ戻す。

## 方針
非正次数では延長の指定成分同型を使い、正次数では零対象の同型を使う。

## 規約
射との自然性も指定成分で照合し、係数比較の順射を保持する。

## 使われ方
等変な鎖ホモトピー逆を、テンソルと余不変を取る関手に適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity
open CategoryTheory Limits HomologicalComplex
variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  (K : CochainComplex C ℤ)

/-- 非正次数での延長の指定成分同型は、元の微分と可換。 -/
lemma nonpositiveExtension_component_d (p q : ℕ) :
    (K.stupidTrunc ComplexShape.embeddingDownNat).d (-(p : ℤ)) (-(q : ℤ)) ≫
      (K.stupidTruncXIso ComplexShape.embeddingDownNat (i := q) rfl).hom =
    (K.stupidTruncXIso ComplexShape.embeddingDownNat (i := p) rfl).hom ≫
      K.d (-(p : ℤ)) (-(q : ℤ)) := by
  change ((K.restriction ComplexShape.embeddingDownNat).extend
    ComplexShape.embeddingDownNat).d (-(p : ℤ)) (-(q : ℤ)) ≫ _ = _
  rw [(K.restriction ComplexShape.embeddingDownNat).extend_d_eq
    ComplexShape.embeddingDownNat (i := p) (j := q)
    (i' := -(p : ℤ)) (j' := -(q : ℤ)) rfl rfl]
  simp only [stupidTruncXIso, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    Category.comp_id, Category.assoc, Iso.inv_hom_id]
  rfl

/-- 非正次数への制限を延長した複体と、元の複体の各次数の指定同型。 -/
def nonpositiveExtensionComponent (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i)) :
    ∀ i : ℤ, (K.stupidTrunc ComplexShape.embeddingDownNat).X i ≅ K.X i
  | .ofNat 0 => K.stupidTruncXIso ComplexShape.embeddingDownNat (i := 0) rfl
  | .ofNat (n + 1) =>
    (K.isZero_stupidTrunc_X ComplexShape.embeddingDownNat ((n + 1 : ℕ) : ℤ) (by
      intro q
      change -(q : ℤ) ≠ ((n + 1 : ℕ) : ℤ)
      omega)).iso (hK ((n + 1 : ℕ) : ℤ) (by omega))
  | .negSucc n => K.stupidTruncXIso ComplexShape.embeddingDownNat (i := n + 1) rfl

/-- 非正次数に集中した複体は、その制限の延長と指定同型を持つ。 -/
def nonpositiveExtensionIso (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i)) :
    K.stupidTrunc ComplexShape.embeddingDownNat ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (nonpositiveExtensionComponent K hK) (by
    intro i j hij
    have hj : i + 1 = j := hij
    subst j
    cases i with
    | ofNat n =>
      exact (hK ((n : ℤ) + 1) (by omega)).eq_of_tgt _ _
    | negSucc n =>
      cases n with
      | zero => exact (nonpositiveExtension_component_d K 1 0).symm
      | succ n =>
        have hj : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
        rw [hj]
        exact (nonpositiveExtension_component_d K (n + 2) (n + 1)).symm)

/-- 指定成分の同型は元の複体の全射に自然である。 -/
lemma nonpositiveExtensionIso_naturality {L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i))
    (hL : ∀ i : ℤ, 0 < i → IsZero (L.X i)) :
    extendMap (restrictionMap f ComplexShape.embeddingDownNat) ComplexShape.embeddingDownNat ≫
      (nonpositiveExtensionIso L hL).hom = (nonpositiveExtensionIso K hK).hom ≫ f := by
  ext i
  simp only [HomologicalComplex.comp_f]
  cases i with
  | ofNat n =>
    cases n with
    | zero =>
      exact stupidTruncMap_stupidTruncXIso_hom f ComplexShape.embeddingDownNat (i := 0) rfl
    | succ n =>
      exact (K.isZero_stupidTrunc_X ComplexShape.embeddingDownNat ((n + 1 : ℕ) : ℤ) (by
        intro q
        change -(q : ℤ) ≠ ((n + 1 : ℕ) : ℤ)
        omega)).eq_of_src _ _
  | negSucc n =>
    exact stupidTruncMap_stupidTruncXIso_hom f ComplexShape.embeddingDownNat (i := n + 1) rfl

end SerrePositivity.EInfinity
