module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorCoefficientSource
public import SerrePositivity.EInfinity.BarrattEccles.Theory.RepresentationFreeBasis

/-!
# 二色の係数の双次数の自由基底

## 概要
HA 3.2.4.7 の二色比較で、テンソル側の各双次数を二色部分群上の自由表現にする。

## 方針
両色の基底の群成分を反転してまとめ、左正則作用を持つ自由軌道基底を得る。

## 規約
基点つき単体の組を固定し、二色部分群は第二の群成分に左乗法で作用する。

## 使われ方
テンソル側の係数解像度の次数ごとの射影性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory
open scoped TensorProduct
variable (A : Type u) [CommRing A]

/-- 二色の実際の係数の一つの双次数。 -/
def twoColorBidegreeRepresentation (m n p q : ℕ) : Rep.{u} A (TwoColorGroup.{u} m n) :=
  (Rep.resFunctor (twoColorLeftProjection m n)).obj ((arityRepresentationChain A m).X p) ⊗
    (Rep.resFunctor (twoColorRightProjection m n)).obj ((arityRepresentationChain A n).X q)

/-- 双次数の二つの群成分と、一つの二色部分群成分との指定添字同型。 -/
def twoColorBidegreeIndexEquiv (m n p q : ℕ) :
    ((ULift.{u} (BasedNondegenerate m p) × Equiv.Perm (Fin m)) ×
      (ULift.{u} (BasedNondegenerate n q) × Equiv.Perm (Fin n))) ≃
    ((ULift.{u} (BasedNondegenerate m p) × ULift.{u} (BasedNondegenerate n q)) ×
      TwoColorGroup.{u} m n) where
  toFun x := ((x.1.1, x.2.1), twoColorGroupEquiv m n (ULift.up (x.1.2⁻¹, x.2.2⁻¹)))
  invFun x := ((x.1.1, ((twoColorGroupEquiv m n).symm x.2).down.1⁻¹),
    (x.1.2, ((twoColorGroupEquiv m n).symm x.2).down.2⁻¹))
  left_inv x := by simp
  right_inv x := by
    rcases x with ⟨⟨a, b⟩, g⟩
    dsimp only
    simp only [inv_inv]
    exact congrArg (fun h => ((a, b), h)) ((twoColorGroupEquiv m n).apply_symm_apply g)

/-- 二色部分群の自由軌道で添字づけた双次数の基底。 -/
def twoColorBidegreeBasis (m n p q : ℕ) :
    Module.Basis ((ULift.{u} (BasedNondegenerate m p) ×
      ULift.{u} (BasedNondegenerate n q)) × TwoColorGroup.{u} m n) A
      (twoColorBidegreeRepresentation A m n p q) :=
  ((equivariantBasis A m p).tensorProduct (equivariantBasis A n q)).reindex
    (twoColorBidegreeIndexEquiv m n p q)

/-- 指定基底の値は、逆群成分を持つ二つの基底ベクトルの純テンソル。 -/
lemma twoColorBidegreeBasis_apply (m n p q : ℕ)
    (i : ULift.{u} (BasedNondegenerate m p) × ULift.{u} (BasedNondegenerate n q))
    (h : TwoColorGroup.{u} m n) :
    twoColorBidegreeBasis A m n p q (i, h) =
      equivariantBasis A m p (i.1, (twoColorLeftProjection m n h).down⁻¹) ⊗ₜ[A]
        equivariantBasis A n q (i.2, (twoColorRightProjection m n h).down⁻¹) := by
  unfold twoColorBidegreeBasis
  erw [Module.Basis.reindex_apply,
    Module.Basis.tensorProduct_apply']
  rfl

/-- 二色の自由軌道基底における群作用の指定公式。 -/
lemma twoColorBidegreeBasis_action (m n p q : ℕ) (g : TwoColorGroup.{u} m n)
    (i : ULift.{u} (BasedNondegenerate m p) × ULift.{u} (BasedNondegenerate n q))
    (h : TwoColorGroup.{u} m n) :
    (twoColorBidegreeRepresentation A m n p q).ρ g
      (twoColorBidegreeBasis A m n p q (i, h)) =
        twoColorBidegreeBasis A m n p q (i, g * h) := by
  rw [twoColorBidegreeBasis_apply, twoColorBidegreeBasis_apply]
  change ((complexRightAction A m (twoColorLeftProjection m n g).down⁻¹).f (-(p : ℤ)))
    (equivariantBasis A m p (i.1, (twoColorLeftProjection m n h).down⁻¹)) ⊗ₜ[A]
    ((complexRightAction A n (twoColorRightProjection m n g).down⁻¹).f (-(q : ℤ)))
      (equivariantBasis A n q (i.2, (twoColorRightProjection m n h).down⁻¹)) = _
  rw [equivariantBasis_rightAction, equivariantBasis_rightAction]
  simp only [map_mul, ULift.mul_down, mul_inv_rev]

/-- 各双次数は、指定された二色の基点つき単体の組上の自由表現。 -/
def twoColorBidegreeFreeIso (m n p q : ℕ) :
    Rep.free A (TwoColorGroup.{u} m n)
      (ULift.{u} (BasedNondegenerate m p) × ULift.{u} (BasedNondegenerate n q)) ≅
      twoColorBidegreeRepresentation A m n p q :=
  representationFreeBasisIso _ (twoColorBidegreeBasis A m n p q)
    (twoColorBidegreeBasis_action A m n p q)

/-- 任意の可換基礎環で、テンソル側の各双次数は射影的。 -/
lemma twoColorBidegree_projective (m n p q : ℕ) :
    Projective (twoColorBidegreeRepresentation A m n p q) :=
  Projective.of_iso (twoColorBidegreeFreeIso A m n p q) inferInstance

end SerrePositivity.EInfinity.BarrattEccles
