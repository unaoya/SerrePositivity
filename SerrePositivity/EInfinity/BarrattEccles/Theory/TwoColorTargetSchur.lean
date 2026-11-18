module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurCoefficientOrder
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoinvariantGroupChange
public import SerrePositivity.EInfinity.BarrattEccles.Theory.ProductCoinvariantComplex

/-!
# 二色係数比較のテンソル側と二つの Schur 成分

HA 3.2.4.7 の自由比較のため、入力と係数の四因子を元の符号つき交換で分離する。
二色部分群から直積群へ指定商写像を保って移し、各因子を実際の Schur 成分へ同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A G : Type u} [CommRing A] [Group G]

/-- 四因子の交換を、元の複体の微分と符号を持つ指定同型として読む。 -/
def representationTensorShuffleIso {K₁ K₂ L₁ L₂ : Complex A}
    (ρ₁ : G →* End K₁) (ρ₂ : G →* End K₂)
    (σ₁ : G →* End L₁) (σ₂ : G →* End L₂) :
    representationCochainComplex (tensorComplexAction (tensorComplexAction ρ₁ ρ₂)
      (tensorComplexAction σ₁ σ₂)) ≅
    representationCochainComplex (tensorComplexAction (tensorComplexAction ρ₁ σ₁)
      (tensorComplexAction ρ₂ σ₂)) :=
  representationCochainIso _ _
    { hom := tensorμ K₁ K₂ L₁ L₂
      inv := tensorδ K₁ K₂ L₁ L₂
      hom_inv_id := tensorμ_tensorδ K₁ K₂ L₁ L₂
      inv_hom_id := tensorδ_tensorμ K₁ K₂ L₁ L₂ }
    (fun g => tensorμ_natural (ρ₁ g).asHom (ρ₂ g).asHom (σ₁ g).asHom (σ₂ g).asHom)

namespace BarrattEccles

/-- 指定二色部分群と、左右の ULift された置換群の直積の同定。 -/
def twoColorProjectionEquiv (m n : ℕ) : TwoColorGroup.{u} m n ≃*
    ULift.{u} (Equiv.Perm (Fin m)) × ULift.{u} (Equiv.Perm (Fin n)) where
  toFun g := (twoColorLeftProjection m n g, twoColorRightProjection m n g)
  invFun g := twoColorGroupEquiv m n (ULift.up (g.1.down, g.2.down))
  left_inv g := by
    change twoColorGroupEquiv m n (ULift.up ((twoColorGroupEquiv m n).symm g).down) = g
    exact (twoColorGroupEquiv m n).apply_symm_apply g
  right_inv g := by
    rcases g with ⟨⟨a⟩, ⟨b⟩⟩
    simp [twoColorLeftProjection, twoColorRightProjection]
  map_mul' g h := by
    ext <;> simp

variable (A : Type u) [CommRing A]

/-- 一つの Schur 成分を、入力と指定係数の対角作用の余不変へ運ぶ。 -/
def schurArityInputCoinvariantIso (X : Complex A) (m : ℕ) :
    arityCoinvariantComplex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A (sequence A) X) m ≅
      tensorCoinvariantComplex (finiteBijectionComplexAction (bijectionFunctor X) m)
        (arityComplexAction A m) :=
  schurArityInputCoefficientIso A X m ≪≫
    coinvariantTensorTotalIso (finiteBijectionComplexAction (bijectionFunctor X) m)
      (arityComplexAction A m)

/-- 入力冪の対称列の作用は、二色部分群の指定左作用を与える。 -/
lemma twoColorLeftInputAction_sequence (X : Complex A) (m n : ℕ) :
    twoColorLeftInputAction X m n =
      (finiteBijectionComplexAction (bijectionFunctor X) m).comp
        (twoColorLeftProjection m n) := by
  apply MonoidHom.ext
  intro g
  apply End.ext
  exact (bijectionFunctor_map_permutation X m (twoColorLeftProjection m n g).down).symm

/-- 入力冪の対称列の作用は、二色部分群の指定右作用を与える。 -/
lemma twoColorRightInputAction_sequence (Y : Complex A) (m n : ℕ) :
    twoColorRightInputAction Y m n =
      (finiteBijectionComplexAction (bijectionFunctor Y) n).comp
        (twoColorRightProjection m n) := by
  apply MonoidHom.ext
  intro g
  apply End.ext
  exact (bijectionFunctor_map_permutation Y n (twoColorRightProjection m n g).down).symm

/-- 二色のテンソル係数の全複体は、二つの実際の Schur 成分のテンソルである。 -/
def twoColorTargetSchurIso (X Y : Complex A) (m n : ℕ) :
    ((twoColorInputTotalFunctor A m n).obj (twoColorSeparatedInput X Y m n)).obj
      (twoColorTargetCochain A m n) ≅
    arityCoinvariantComplex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A (sequence A) X) m ⊗
      arityCoinvariantComplex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A (sequence A) Y) n := by
  let ρ := finiteBijectionComplexAction (bijectionFunctor X) m
  let σ := finiteBijectionComplexAction (bijectionFunctor Y) n
  let α := arityComplexAction A m
  let β := arityComplexAction A n
  let e := twoColorProjectionEquiv m n
  let T := Rep.coinvariantsFunctor A (TwoColorGroup.{u} m n)
  have hρ := twoColorLeftInputAction_sequence A X m n
  have hσ := twoColorRightInputAction_sequence A Y m n
  refine coinvariantTensorTotalIso (tensorComplexAction (twoColorLeftInputAction X m n)
    (twoColorRightInputAction Y m n)) (tensorComplexAction (twoColorLeftAction A m n)
      (twoColorRightAction A m n)) ≪≫ ?_
  refine (T.mapHomologicalComplex (.up ℤ)).mapIso
    (representationTensorShuffleIso (twoColorLeftInputAction X m n)
      (twoColorRightInputAction Y m n) (twoColorLeftAction A m n)
      (twoColorRightAction A m n)) ≪≫ ?_
  let R := representationCochainComplex (tensorComplexAction
    ((tensorComplexAction ρ α).comp
      (MonoidHom.fst (ULift.{u} (Equiv.Perm (Fin m))) (ULift.{u} (Equiv.Perm (Fin n)))))
    ((tensorComplexAction σ β).comp
      (MonoidHom.snd (ULift.{u} (Equiv.Perm (Fin m))) (ULift.{u} (Equiv.Perm (Fin n))))))
  have h : representationCochainComplex (tensorComplexAction
      (tensorComplexAction (twoColorLeftInputAction X m n) (twoColorLeftAction A m n))
      (tensorComplexAction (twoColorRightInputAction Y m n) (twoColorRightAction A m n))) =
      ((Rep.resFunctor e.toMonoidHom).mapHomologicalComplex (.up ℤ)).obj R := by
    rw [hρ, hσ]
    rfl
  exact (T.mapHomologicalComplex (.up ℤ)).mapIso (eqToIso h) ≪≫
    coinvariantGroupChangeComplexIso e R ≪≫
    productCoinvariantComplexIso (tensorComplexAction ρ α) (tensorComplexAction σ β) ≪≫
    tensorIso (schurArityInputCoinvariantIso A X m).symm
      (schurArityInputCoinvariantIso A Y n).symm

end BarrattEccles
end SerrePositivity.EInfinity
