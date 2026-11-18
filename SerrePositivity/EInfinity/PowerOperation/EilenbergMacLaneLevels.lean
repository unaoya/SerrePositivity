module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.TruncatedDoldKanFunctor
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Eilenberg–Mac Lane の各段の実 Dold–Kan 模型

DAG XIII §2.2、BS Lemma 8.4 のスペクトル忘却への前段。
第 n 段は M[n] の非正 smart 切断に実 Γ を適用する。
正規化との比較は同じ Dold–Kan 随伴の余単位であり、構造射や Ω 条件は後続で作る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 第 n 段の smart 切断を非負鎖複体として読む全関手。 -/
def levelChainFunctor (n : ℕ) : Complex A ⥤ ChainComplex (ModuleCat A) ℕ :=
  shiftFunctor (Complex A) (n : ℤ) ⋙
    (ComplexShape.embeddingUpIntLE 0).truncLE'Functor (ModuleCat A)

/-- 同じ切断に実 Γ を適用した単体的加群の全関手。 -/
def levelModuleFunctor (n : ℕ) : Complex A ⥤ SimplicialObject (ModuleCat A) :=
  levelChainFunctor A n ⋙ (Abelian.DoldKan.Γ :
    ChainComplex (ModuleCat A) ℕ ⥤ SimplicialObject (ModuleCat A))

/-- 単体的加群から台を読んだ各段の全関手。 -/
def levelSpaceFunctor (n : ℕ) : Complex A ⥤ SSet.{u} :=
  shiftFunctor (Complex A) (n : ℤ) ⋙ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A

/-- 台の段の関手も、指定された同じ単体的加群の台である。 -/
lemma levelSpaceFunctor_eq (n : ℕ) :
    levelSpaceFunctor A n = levelModuleFunctor A n ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat A) (Type u)).obj
        (forget (ModuleCat A)) := rfl

/-- 正規化は、別の模型でなく指定 smart 切断へ自然同型で戻る。 -/
def normalizedLevelIso (n : ℕ) :
    levelModuleFunctor A n ⋙ (Abelian.DoldKan.N :
      SimplicialObject (ModuleCat A) ⥤ ChainComplex (ModuleCat A) ℕ) ≅
        levelChainFunctor A n :=
  Functor.isoWhiskerLeft (levelChainFunctor A n)
    (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
      ChainComplex (ModuleCat A) ℕ).counitIso

end SerrePositivity.EInfinity.PowerOperation
