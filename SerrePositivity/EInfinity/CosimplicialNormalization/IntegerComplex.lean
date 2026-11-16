module

public import SerrePositivity.EInfinity.CosimplicialNormalization.NatFunctor
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# 同じ正規化余単体的複体の整数次数への零延長

Dold–Kanの正規化とBerger–Fresse §2.2、M14 L20、報告 §397。
元の自然数複体と包含を同じembeddingUpNatの延長関手へ送る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.CosimplicialNormalization
open CategoryTheory HomologicalComplex AlgebraicTopology
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 同じ正規化核の整数コチェイン複体の関手（Dold–Kan、BF §2.2）。 -/
def normalizedCochainFunctor : CosimplicialObject (ModuleCat.{u} A) ⥤ Complex A :=
  normalizedCochainNatFunctor A ⋙ ComplexShape.embeddingUpNat.extendFunctor (ModuleCat A)

/-- 整数の非負次数は元の同じcodegeneracy核と標準比較される（Dold–Kan、BF §2.2）。 -/
def normalizedCochainXIso (X : CosimplicialObject (ModuleCat.{u} A)) (q : ℕ) :
    ((normalizedCochainFunctor A).obj X).X (q : ℤ) ≅ ModuleCat.of A (normalizedSubmodule A X q) :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat rfl

/-- 元の交代余面複体の整数零延長の関手（Dold–Kan、BF §2.2）。 -/
def unnormalizedCochainFunctor : CosimplicialObject (ModuleCat.{u} A) ⥤ Complex A :=
  alternatingCofaceMapComplex (ModuleCat A) ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ModuleCat A)

/-- 同じ部分加群の包含を全整数で読む自然変換（Dold–Kan、BF §2.2）。 -/
def normalizationInclusion : normalizedCochainFunctor A ⟶ unnormalizedCochainFunctor A :=
  Functor.whiskerRight (normalizationInclusionNat A)
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat A))

/-- 元の指定された正規化包含（Dold–Kan、BF §2.2）。 -/
def normInclusion (X : CosimplicialObject (ModuleCat.{u} A)) :
    (normalizedCochainFunctor A).obj X ⟶ (unnormalizedCochainFunctor A).obj X :=
  (normalizationInclusion A).app X

/-- L20：同じ指定包含は全整数で微分と可換（Dold–Kan、BF §2.2）。 -/
lemma normInclusion_d (X : CosimplicialObject (ModuleCat.{u} A)) (i j : ℤ) :
    ((normalizedCochainFunctor A).obj X).d i j ≫ (normInclusion A X).f j =
      (normInclusion A X).f i ≫ ((unnormalizedCochainFunctor A).obj X).d i j :=
  ((normInclusion A X).comm i j).symm

/-- L20：同じ指定包含は元の全余単体的写像に自然（Dold–Kan、BF §2.2）。 -/
lemma normInclusion_naturality {X Y : CosimplicialObject (ModuleCat.{u} A)} (f : X ⟶ Y) :
    (normalizedCochainFunctor A).map f ≫ normInclusion A Y =
      normInclusion A X ≫ (unnormalizedCochainFunctor A).map f :=
  (normalizationInclusion A).naturality f

end SerrePositivity.EInfinity.CosimplicialNormalization
