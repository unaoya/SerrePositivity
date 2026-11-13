module
public import SerrePositivity.KST.SConstruction.McCarthyRho
public import SerrePositivity.KST.SConstruction.McCarthySpanEvaluations
public import SerrePositivity.KST.SConstruction.PointwisePushoutEvaluation

/-! # McCarthy の ρ の subobject と quotient の厳密回収
概要：元の C 内で選んだ ρ の subobject は μ の subobject、quotient は E の quotient。
方針：各角で評価した恒等 span に正規化した同じ押し出し選択を適用する。
規約：同型に弱めない。使われ方：左 fiber 内の実ホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：raw ρ の subobject は動かした Ar 添字での A の制限。
方針：左枝が恒等な span の同じ押し出し選択の正規化。
規約：元の C 内の図式の厳密等号。使われ方：左 fiber の基底条件。 -/
lemma mcCarthyRhoRaw_source {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) :
    mcCarthyRhoRaw z A α τ E h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm 0) =
      arNerveMap (mcCarthyMovedOrder α τ) ≫ A := by
  rw [mcCarthyRhoRaw, pointwiseDiagramPushoutApex_evaluate]
  rw [Category.assoc, ← cofiberProjection_source, mcCarthySpan_source,
    curry_identitySpan, pointwisePushoutApex_identity, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval,
    ← Category.assoc, mcCarthyArMotion_one]

/-- 概要：cofiber 値の ρ の subobject は動かした添字の A。
方針：包含で raw ρ を回収して各角の等号を使う。
規約：cofiber 図式の入力の始点の厳密な等号。使われ方：左 fiber 内の族の構成。 -/
lemma mcCarthyRho_source {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) :
    mcCarthyRho z A α τ E h ≫ cofiberProjection C ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap (mcCarthyMovedOrder α τ) ≫ A := by
  rw [cofiberProjection_source, ← Category.assoc, mcCarthyRho_ι, mcCarthyRhoRaw_source]

/-- 概要：raw ρ の quotient は元の E の quotient。
方針：上枝が恒等な span の同じ押し出し選択の正規化。
規約：全高次単体で厳密に回収する。使われ方：quotient 上のホモトピーの条件。 -/
lemma mcCarthyRhoRaw_quotient {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) :
    mcCarthyRhoRaw z A α τ E h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm 1) =
      E ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm 1) := by
  rw [mcCarthyRhoRaw, pointwiseDiagramPushoutApex_evaluate, Category.assoc,
    mcCarthySpan_quotient, curry_identitySpan, pointwisePushoutApex_identity,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, ← Category.assoc, ← Category.assoc,
    mcCarthyLambdaNu_one, Category.assoc]

/-- 概要：cofiber 値の ρ の quotient は元の E の quotient。
方針：包含による raw ρ の回収と quotient の正規化の式。
規約：射の厳密な等号。使われ方：McCarthy の quotient への射の固定。 -/
lemma mcCarthyRho_quotient {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) :
    mcCarthyRho z A α τ E h ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm 1) =
      E ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm 1) := by
  rw [← Category.assoc, mcCarthyRho_ι, mcCarthyRhoRaw_quotient]

end SerrePositivity.KST.SConstruction
