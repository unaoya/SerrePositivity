module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurComplexArity
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoinvariantTensorComplex

/-!
# 実際の Schur 複体とテンソル余不変の全複体

Berger–Moerdijk §1 の Schur 図式の対角作用を同定し、HA 3.2.4.7 の自由比較で
使う全複体の表示へ移す。指定商写像と直和包含を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A] (P : SymmetricSequence (Complex A)) (K : Complex A)

/-- 実際の Schur 図式の作用は、係数と入力の二つの作用の対角作用である。 -/
lemma schurDiagramComplexAction (n : ℕ) :
    finiteBijectionComplexAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K) n =
      tensorComplexAction (finiteBijectionComplexAction P n)
        (finiteBijectionComplexAction (bijectionFunctor K) n) := by
  ext g
  rfl

/-- 一つの arity の指定商は、テンソル余不変の全複体に同定される。 -/
def schurArityTotalIso (n : ℕ) :
    arityCoinvariantComplex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K) n ≅
      coinvariantTensorTotal (finiteBijectionComplexAction P n)
        (finiteBijectionComplexAction (bijectionFunctor K) n) :=
  ((Rep.coinvariantsFunctor A (ULift.{u} (Equiv.Perm (Fin n)))).mapHomologicalComplex
    (.up ℤ)).mapIso (eqToIso (congrArg representationCochainComplex
      (schurDiagramComplexAction P K n))) ≪≫
    (coinvariantTensorTotalIso (finiteBijectionComplexAction P n)
      (finiteBijectionComplexAction (bijectionFunctor K) n)).symm

/-- 元の Schur 複体の、全整数次数と両方の微分を保つ arity ごとの全複体表示。 -/
def schurArityTotalIsoSum :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P).obj K ≅ ∐ (fun n : ℕ =>
      coinvariantTensorTotal (finiteBijectionComplexAction P n)
        (finiteBijectionComplexAction (bijectionFunctor K) n)) :=
  schurComplexArityIso P K ≪≫ Sigma.mapIso (schurArityTotalIso P K)

/-- 元の Schur 生成元は、指定 arity 商の後の指定成分と直和包含へ送られる。 -/
lemma schurArityTotalIsoSum_ι (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n ≫ (schurArityTotalIsoSum P K).hom =
      arityCoinvariantComplexQuotient (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K) n ≫
        (schurArityTotalIso P K n).hom ≫
          Sigma.ι (fun r : ℕ => coinvariantTensorTotal (finiteBijectionComplexAction P r)
            (finiteBijectionComplexAction (bijectionFunctor K) r)) n := by
  change colimit.ι (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K) (FiniteBijection.of n) ≫
    ((arityCoinvariantComplexIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K)).hom ≫
      (Sigma.mapIso (schurArityTotalIso P K)).hom) = _
  rw [← Category.assoc, arityCoinvariantComplexIso_ι, Category.assoc, Sigma.ι_mapIso_hom]

end SerrePositivity.EInfinity
