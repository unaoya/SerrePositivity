module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseDifferential
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# 微分を消す操作と次数付きのモノイダル比較

## 概要
Berger–Moerdijk 命題 4.1 のセル付加で、次数付き対象への忠実な忘却を使う。

## 方針
Mathlib の忘却の強モノイダル構造を保持し、比較射との可換性だけを次数ごとに確認する。

## 規約
選択された余積の間の比較射を式に残す。

## 使われ方
微分を消す関手のモノイダル構造と代数の自由表示。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded
open Functor.LaxMonoidal
variable (A : Type u) [CommRing A]
local notation "U" => HomologicalComplex.forget (ModuleCat A) (ComplexShape.up ℤ)

/-- The existing strong monoidal structure on the graded forgetful functor. -/
@[instance_reducible]
def complexGradedForgetMonoidal : (U).Monoidal :=
  Monoidal.fromInducedMonoidal (U)
    (HomologicalComplex.Monoidal.inducingFunctorData (ModuleCat A) (.up ℤ))

attribute [local instance] complexGradedForgetMonoidal

@[simp]
lemma eraseDifferential_forget_map {K L : Complex A} (f : K ⟶ L) :
    (U).map ((eraseDifferential A).map f) = (U).map f := rfl

@[simp]
lemma eraseDifferentialTensorIso_forget_hom (K L : Complex A) :
    (U).map (eraseDifferentialTensorIso A K L).hom =
      (U).map (𝟙 (K ⊗ L)) := by
  funext i
  exact eraseDifferentialTensorIso_hom_f A K L i

@[simp]
lemma eraseDifferentialUnitIso_forget_hom :
    (U).map (eraseDifferentialUnitIso A).hom =
      (U).map (𝟙 (𝟙_ (Complex A))) := by
  funext i
  exact eraseDifferentialUnitIso_hom_f A i

/-- The tensor comparisons commute before identifying the chosen graded coproducts. -/
@[reassoc]
lemma eraseDifferential_forget_tensor (K L : Complex A) :
    μ (U) ((eraseDifferential A).obj K) ((eraseDifferential A).obj L) ≫
        (U).map (eraseDifferentialTensorIso A K L).hom = μ (U) K L := by
  funext i
  change 𝟙 _ ≫ (eraseDifferentialTensorIso A K L).hom.f i = 𝟙 _
  rw [eraseDifferentialTensorIso_hom_f, Category.id_comp]

/-- The unit comparison commutes with the fixed graded unit comparison. -/
@[reassoc]
lemma eraseDifferential_forget_unit :
    ε (U) ≫ (U).map (eraseDifferentialUnitIso A).hom = ε (U) := by
  funext i
  change (ε (U)) i ≫ (eraseDifferentialUnitIso A).hom.f i = (ε (U)) i
  rw [eraseDifferentialUnitIso_hom_f]
  rfl

end SerrePositivity.EInfinity
