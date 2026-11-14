module

public import SerrePositivity.EInfinity.SimplexCuts.ComponentLeibniz

/-!
# 一般の単体鎖の切断余演算の複体射

Berger–Fresse §2.2.6–7。全 arity・全整数の同じ切断成分の微分公式から
既存の tensorLift で複体射を作る。対称性・単位・合成の法則は後続で証明する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

/-- 同じ双線形切断成分を、元の加群テンソルの射として読む（BF §2.2.6）。 -/
def cochainActionComponent (S : SSet.{0}) (r : ℕ) (i j t : ℤ) (h : i + j = t) :
    (Surjection.complex A r).X i ⊗ (chains A S).X j ⟶ (power (chains A S) r).X t :=
  ModuleCat.ofHom (TensorProduct.lift (component A S r i j t h))

/-- C316：同じ斉次テンソル成分の微分の法則（BF §2.2.7）。 -/
lemma cochainActionComponent_d (S : SSet.{0}) (r : ℕ) (i j : ℤ) :
    cochainActionComponent A S r i j (i + j) rfl ≫
        (power (chains A S) r).d (i + j) (i + j + 1) =
      ((Surjection.complex A r).d i (i + 1) ▷ (chains A S).X j) ≫
        cochainActionComponent A S r (i + 1) j (i + j + 1) (by omega) +
      i.negOnePow • (((Surjection.complex A r).X i ◁ (chains A S).d j (j + 1)) ≫
        cochainActionComponent A S r i (j + 1) (i + j + 1) (by omega)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  exact component_d A S r i j a b

/-- 同じ切断成分の全 arity の実際の整数複体射（BF §2.2.6–7）。 -/
def cochainAction (S : SSet.{0}) (r : ℕ) :
    Surjection.complex A r ⊗ chains A S ⟶ power (chains A S) r :=
  tensorLift (cochainActionComponent A S r) (cochainActionComponent_d A S r)

/-- C317：構成した複体射の斉次成分は、指定した元の切断成分（BF §2.2.6）。 -/
@[reassoc (attr := simp)] lemma ι_cochainAction (S : SSet.{0}) (r : ℕ)
    (i j t : ℤ) (h : i + j = t) :
    ιTensorObj (Surjection.complex A r) (chains A S) i j t h ≫
      (cochainAction A S r).f t = cochainActionComponent A S r i j t h :=
  ι_tensorLift _ _ i j t h

end SerrePositivity.EInfinity.SimplexCuts
