module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ComponentLeibniz

/-!
模型。文献の定義との比較は後で
# 一般の単体鎖の切断余演算の複体射

Berger–Fresse §2.2.6–7。全 arity・全整数の同じ切断成分の微分公式から
既存の tensorLift で複体射を作る。対称性・単位・合成の法則は後続で証明する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

/-- 同じ双線形切断成分を、元の加群テンソルの射として読む（BF §2.2.6）。 -/
def cochainActionComponent (S : SSet.{0}) (r : ℕ) (i j t : ℤ) (h : i + j = t) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A r).X i ⊗ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X j ⟶ (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r).X t :=
  ModuleCat.ofHom (TensorProduct.lift (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.component A S r i j t h))

/-- C316：同じ斉次テンソル成分の微分の法則（BF §2.2.7）。 -/
lemma cochainActionComponent_d (S : SSet.{0}) (r : ℕ) (i j : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainActionComponent A S r i j (i + j) rfl ≫
        (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r).d (i + j) (i + j + 1) =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A r).d i (i + 1) ▷ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X j) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainActionComponent A S r (i + 1) j (i + j + 1) (by omega) +
      i.negOnePow • (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A r).X i ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).d j (j + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainActionComponent A S r i (j + 1) (i + j + 1) (by omega)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.component_d A S r i j a b

/-- 同じ切断成分の全 arity の実際の整数複体射（BF §2.2.6–7）。 -/
def cochainAction (S : SSet.{0}) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A r ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S ⟶ power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r :=
  tensorLift (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainActionComponent A S r) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainActionComponent_d A S r)

/-- C317：構成した複体射の斉次成分は、指定した元の切断成分（BF §2.2.6）。 -/
@[reassoc (attr := simp)] lemma ι_cochainAction (S : SSet.{0}) (r : ℕ)
    (i j t : ℤ) (h : i + j = t) :
    ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A r) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) i j t h ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S r).f t = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainActionComponent A S r i j t h :=
  ι_tensorLift _ _ i j t h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
