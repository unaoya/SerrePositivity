module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ResolutionCandidateFunctor
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-!
# 同じ半自由分解候補の複体上の関手

## 概要
一対象 DG 加群と複体との既存の同値を介して、同じ候補を複体へ戻す。

## 方針
増大は既存の増大と同値の余単位の合成。半自由性・擬同型性は既存の証明を使う。

## 規約
加法性は主張しない。余単体的図式へ適用した後に交代余面複体を作る。

## 使われ方
BS 著者版 Lemma 4.22 の厳密な K-flat 行模型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonResolution
variable (R : Type u) [CommRing R]

/-- 同じ半自由候補を複体の同値で戻した関手。 -/
def complexResolutionFunctor : Complex R ⥤ Complex R :=
  (ringModuleEquivalence R).inverse ⋙ candidateFunctor R PUnit.{1} ⋙
    (ringModuleEquivalence R).functor

/-- 元の増大と同値の余単位からなる指定の増大。 -/
def complexResolutionAugmentation : complexResolutionFunctor R ⟶ 𝟭 (Complex R) where
  app K := (ringModuleEquivalence R).functor.map
      ((candidateAugmentation R PUnit.{1}).app ((ringModuleEquivalence R).inverse.obj K)) ≫
    (ringModuleEquivalence R).counitIso.hom.app K
  naturality K L g := by
    change (ringModuleEquivalence R).functor.map
        ((candidateFunctor R PUnit.{1}).map ((ringModuleEquivalence R).inverse.map g)) ≫ _ = _
    rw [← Category.assoc, ← Functor.map_comp]
    rw [(candidateAugmentation R PUnit.{1}).naturality ((ringModuleEquivalence R).inverse.map g)]
    rw [Functor.map_comp, Category.assoc]
    simp only [Functor.id_map]
    have hn := (ringModuleEquivalence R).counitIso.hom.naturality g
    simp only [Functor.comp_map, Functor.id_map] at hn
    rw [hn]
    exact (Category.assoc _ _ _).symm

/-- 各行は本体の同じ半自由複体である。 -/
theorem complexResolutionFunctor_semifree (K : Complex R) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree R
      ((complexResolutionFunctor R).obj K) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree_evaluation R
    ((candidateFunctor R PUnit.{1}).obj ((ringModuleEquivalence R).inverse.obj K))).mpr
      (candidateFunctor_semifree R PUnit.{1} _)

/-- 各行の K-flat 性は既存の半自由性から従う。 -/
theorem complexResolutionFunctor_kFlat (K : Complex R) :
    complexKFlat R ((complexResolutionFunctor R).obj K) :=
  semifreeComplex_isKFlat (complexResolutionFunctor_semifree R K)

/-- 同じ指定増大は各複体上で擬同型である。 -/
theorem complexResolutionAugmentation_quasiIso (K : Complex R) :
    QuasiIso ((complexResolutionAugmentation R).app K) := by
  haveI : QuasiIso ((ringModuleEquivalence R).functor.map
      ((candidateAugmentation R PUnit.{1}).app ((ringModuleEquivalence R).inverse.obj K))) :=
    (ringModuleQuasiIso_iff R _).mp (candidateAugmentation_quasiIso R PUnit.{1} _)
  change QuasiIso ((ringModuleEquivalence R).functor.map
      ((candidateAugmentation R PUnit.{1}).app ((ringModuleEquivalence R).inverse.obj K)) ≫
    (ringModuleEquivalence R).counitIso.hom.app K)
  infer_instance

end SerrePositivity.BhattScholze.Prismatic.HTComparisonResolution
