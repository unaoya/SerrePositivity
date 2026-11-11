module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorBidegreeBasis
public import SerrePositivity.EInfinity.BarrattEccles.Degrees

/-!
# 二色のテンソル係数の次数ごとの射影性

## 概要
HA 3.2.4.7 の二色比較のテンソル係数は、二色部分群上で次数ごとに射影的である。

## 方針
非正の双次数には自由軌道基底を使い、正次数を含む双次数を零として除く。

## 規約
テンソルは実際のコチェイン複体のテンソルで、双次数の指定包含を保つ。

## 使われ方
二色のテンソル係数の射影解像度。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A]

/-- 第一の色の実際の複体の二色部分群作用。 -/
def twoColorLeftAction (m n : ℕ) : TwoColorGroup.{u} m n →* End (complex A m) :=
  (arityComplexAction A m).comp (twoColorLeftProjection m n)

/-- 第二の色の実際の複体の二色部分群作用。 -/
def twoColorRightAction (m n : ℕ) : TwoColorGroup.{u} m n →* End (complex A n) :=
  (arityComplexAction A n).comp (twoColorRightProjection m n)

/-- 複体の台が零である次数の表現も零である。 -/
lemma representationDegree_isZero {G : Type u} [Group G]
    {K : CochainComplex (ModuleCat.{u} A) ℤ} (ρ : G →* End K) (i : ℤ)
    (hi : IsZero (K.X i)) : IsZero (Rep.of (complexDegreeRepresentation ρ i)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (forget₂ (Rep.{u} A G) (ModuleCat.{u} A)).map_injective
  simpa using (IsZero.iff_id_eq_zero _).mp hi

/-- 各双次数の二色係数表現は射影的である。 -/
lemma twoColorTensorSummand_projective (m n : ℕ) (i : ℤ)
    (a : {a : ℤ × ℤ // a.1 + a.2 = i}) :
    Projective (tensorDegreeRepresentationSummand
      (twoColorLeftAction A m n) (twoColorRightAction A m n) i a) := by
  by_cases h₁ : 0 < a.1.1
  · have hz := representationDegree_isZero A (twoColorLeftAction A m n) a.1.1
      (complex_isZero_positive A m a.1.1 h₁)
    exact ((tensorRight (Rep.of (complexDegreeRepresentation
      (twoColorRightAction A m n) a.1.2))).map_isZero hz).projective
  by_cases h₂ : 0 < a.1.2
  · have hz := representationDegree_isZero A (twoColorRightAction A m n) a.1.2
      (complex_isZero_positive A n a.1.2 h₂)
    exact ((tensorLeft (Rep.of (complexDegreeRepresentation
      (twoColorLeftAction A m n) a.1.1))).map_isZero hz).projective
  have e₁ : a.1.1 = -((-a.1.1).toNat : ℤ) := by omega
  have e₂ : a.1.2 = -((-a.1.2).toNat : ℤ) := by omega
  change Projective (Rep.of (complexDegreeRepresentation (twoColorLeftAction A m n) a.1.1) ⊗
    Rep.of (complexDegreeRepresentation (twoColorRightAction A m n) a.1.2))
  rw [e₁, e₂]
  exact twoColorBidegree_projective A m n (-a.1.1).toNat (-a.1.2).toNat

/-- 実際のテンソル係数の全次数は二色部分群上で射影的である。 -/
lemma twoColorTensorDegree_projective (m n : ℕ) (i : ℤ) :
    Projective (Rep.of (complexDegreeRepresentation
      (tensorComplexAction (twoColorLeftAction A m n) (twoColorRightAction A m n)) i)) := by
  let F := tensorDegreeRepresentationSummand (twoColorLeftAction A m n)
    (twoColorRightAction A m n) i
  let h := tensorDegreeRepresentationIsColimit (twoColorLeftAction A m n)
    (twoColorRightAction A m n) i
  refine ⟨fun {E X} f e he => ?_⟩
  have lifts (a : {a : ℤ × ℤ // a.1 + a.2 = i}) :
      ∃ l : F a ⟶ E, l ≫ e = tensorDegreeRepresentationLeg
        (twoColorLeftAction A m n) (twoColorRightAction A m n) i a ≫ f := by
    have := twoColorTensorSummand_projective A m n i a
    exact Projective.factors _ e
  choose l hl using lifts
  refine ⟨h.desc (Cofan.mk E l), ?_⟩
  apply Cofan.IsColimit.hom_ext h
  intro a
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ e) (h.fac (Cofan.mk E l) ⟨a⟩)).trans (hl a))

end SerrePositivity.EInfinity.BarrattEccles
