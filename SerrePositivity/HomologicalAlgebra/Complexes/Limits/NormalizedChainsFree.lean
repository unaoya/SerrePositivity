module

public import SerrePositivity.EInfinity.BarrattEccles.Basis
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# 任意の単体集合の正規化鎖の自由加群表示

概要：元の正規化 Moore 複体の各鎖次数は非退化単体上の自由加群。
方針：同じ単体集合の splitting を線形化し、Karoubi の実比較を戻す。
規約：単体集合は元の小さい宇宙、係数環・加群は任意の宇宙。
使われ方：正規化境界の射影 cofibration 判定。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Idempotents
open _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

def normalizedLinearSplitting (X : SSet.{0}) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X).Splitting := by
  letI := (ModuleCat.adj A).isLeftAdjoint
  exact X.splitting.map (uliftFunctor.{u, 0} ⋙ ModuleCat.free A)

def normalizedNondegenerateChainIso (X : SSet.{0}) :
    (_root_.SerrePositivity.ComplexLimits.normalizedLinearSplitting A X).nondegComplex ≅
      (AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X) :=
  (toKaroubi _).preimageIso
    ((_root_.SerrePositivity.ComplexLimits.normalizedLinearSplitting A X).toKaroubiNondegComplexIsoN₁ ≪≫
      (AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi
        (ModuleCat A)).app _)

def normalizedChainFreeIso (X : SSet.{0}) (n : ℕ) :
    ((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X)).X n ≅
        (ModuleCat.free A).obj (ULift.{u} (X.nonDegenerate n)) :=
  (HomologicalComplex.eval _ _ n).mapIso (_root_.SerrePositivity.ComplexLimits.normalizedNondegenerateChainIso A X).symm

lemma normalizedChain_projective (X : SSet.{0}) (n : ℕ) :
    Projective (((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X)).X n) :=
  Projective.of_iso (_root_.SerrePositivity.ComplexLimits.normalizedChainFreeIso A X n).symm
    (ModuleCat.projective_of_free (Finsupp.basisSingleOne :
      Module.Basis (ULift.{u} (X.nonDegenerate n)) A (ULift.{u} (X.nonDegenerate n) →₀ A)))

end SerrePositivity.ComplexLimits
