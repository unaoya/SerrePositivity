module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Poincare.CrystallineExtraContraction
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedPushout
public import Mathlib.Algebra.Category.Ring.Under.Basic
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineReductionPushout
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedPushout
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.SplitCechConerve
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Poincare.CrystallineExtraContraction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 余分な反復 δ 座標の Čech 因子

## 概要
自由 pd Čech 模型に、高次 δ 座標の多項式 Čech 余脈体を加える。

## 方針
多項式の座標を零に評価する切断を使い、係数環上の余積と完備化にホモトピーを施す。

## 規約
高次 δ 座標は δ^{a+1} の a で添字付ける。

## 使われ方
余分な反復 δ 座標を除いたモデルとの mod p 比較。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits SerrePositivity.Cosimplicial
open SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (k : Type u) [CommRing k] (r : ℕ)

local notation "K" => CommRingCat.of k
local notation "A" => Under (CommRingCat.of k)

/-- 頂点ごとに置く正の反復 δ 座標の多項式環。 -/
abbrev extraVariables (n : ℕ) := MvPolynomial ((Fin r × ℕ) × Fin (n + 1)) k

private abbrev baseObject : A := Under.mk (𝟙 K)
private def coordObject : A := CommRingCat.mkUnder K (MvPolynomial (Fin r × ℕ) k)

private abbrev extraCechArrow : Arrow A :=
  Arrow.mk (Under.homMk (coordObject k r).hom (Category.id_comp _)
    : baseObject k ⟶ coordObject k r)

private def extraCechSection : (extraCechArrow k r).right ⟶ (extraCechArrow k r).left :=
  Under.homMk (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0))) (by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact MvPolynomial.eval₂Hom_C _ _ _)

private theorem extraCechSection_comp :
    (extraCechArrow k r).hom ≫ extraCechSection k r = 𝟙 (extraCechArrow k r).left := by
  apply Under.UnderMorphism.ext
  exact (extraCechSection k r).w

/-- 正の反復 δ 座標を頂点ごとに加える Čech 余脈体。 -/
def extraCech : CosimplicialObject CommRingCat.{u} :=
  (extraCechArrow k r).cechConerve ⋙ Under.forget K

/-- 未完備の pd 模型と高次座標の Čech 因子との余積。 -/
def crystallineExtraRaw : CosimplicialAlgebra k :=
  (pdRawModel k r).prod' (extraCechArrow k r).cechConerve ⋙ crystallineAlgebraCoprod

/-- 自由 pd 模型に各頂点の正の反復 δ 座標を加え、p 完備化する。 -/
def withExtraCoords (p : ℕ) (k : Type u) [CommRing k] (r : ℕ) : CosimplicialAlgebra k :=
  crystallineExtraRaw k r ⋙ principalCompletionUnder p (CommRingCat.of k)

private theorem baseHom_unique {X : A} (f g : baseObject k ⟶ X) : f = g := by
  apply Under.UnderMorphism.ext
  have hf : 𝟙 K ≫ f.right = X.hom := f.w
  have hg : 𝟙 K ≫ g.right = X.hom := g.w
  rw [Category.id_comp] at hf hg
  exact hf.trans hg.symm

private def baseCoprodApp (X : A) : X ≅ X ⨿ baseObject k where
  hom := coprod.inl
  inv := coprod.desc (𝟙 X) (Under.homMk X.hom (Category.id_comp _))
  hom_inv_id := coprod.inl_desc _ _
  inv_hom_id := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc, Category.id_comp, Category.comp_id]
    · exact baseHom_unique k _ _

private def baseCoprodIso :
    pdRawModel k r ≅
      (pdRawModel k r).prod' ((Functor.const SimplexCategory).obj (baseObject k)) ⋙
        crystallineAlgebraCoprod :=
  NatIso.ofComponents (fun n => baseCoprodApp k ((pdRawModel k r).obj n))
    (fun {_ _} θ => by
      change (pdRawModel k r).map θ ≫ coprod.inl = coprod.inl ≫
        coprod.map ((pdRawModel k r).map θ) (𝟙 (baseObject k))
      exact (coprod.inl_map _ _).symm)

private def rawInsertPdFactor : pdRawModel k r ⟶ crystallineExtraRaw k r :=
  (baseCoprodIso k r).hom ≫ crystallineAddSplitCech (extraCechArrow k r) (pdRawModel k r)

/-- 完備 pd 模型から余分な座標を持つ模型への包含。 -/
def insertPdFactor (p : ℕ) (k : Type u) [CommRing k] (r : ℕ) :
    pdModel p k r ⟶ withExtraCoords p k r :=
  Functor.whiskerRight (rawInsertPdFactor k r) (principalCompletionUnder p (CommRingCat.of k))

def crystallineReducePrime (p : ℕ) : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj := crystallineModPrimeRing p
  map := crystallineModPrimeRingMap p
  map_id R := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  map_comp f g := (ringMap_comp (p := p) f g).symm

/-- 余分な座標の因子を加えても mod p のコホモロジーは変わらない。 -/
theorem insertPdFactorModP_isCohomologyIso (p : ℕ) :
    IsCohomologyIso (Functor.whiskerRight (insertPdFactor p k r)
      (Under.forget K ⋙ crystallineReducePrime p)) := by
  intro n
  let F := principalCompletionUnder p K ⋙ Under.forget K ⋙ crystallineReducePrime p ⋙
    forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let L := AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat
  let E := cechSplitCochainEquiv (extraCechArrow k r) (extraCechSection k r)
    (extraCechSection_comp k r) (pdRawModel k r) (crystallineAlgebraCoprod ⋙ F)
  let I := L.mapIso (Functor.isoWhiskerRight (baseCoprodIso k r) F)
  let e := (HomotopyEquiv.ofIso I).trans E
  have h : e.hom = L.map (Functor.whiskerRight (rawInsertPdFactor k r) F) := by
    change L.map (Functor.whiskerRight (baseCoprodIso k r).hom F) ≫
      L.map (Functor.whiskerRight (crystallineAddSplitCech (extraCechArrow k r) (pdRawModel k r)) F) =
      L.map (Functor.whiskerRight (rawInsertPdFactor k r) F)
    erw [← L.map_comp, ← Functor.whiskerRight_comp]
    rfl
  have hb := ConcreteCategory.bijective_of_isIso (e.toHomologyIso n).hom
  change Function.Bijective (HomologicalComplex.homologyMap e.hom n).hom at hb
  rw [h] at hb
  exact hb

end SerrePositivity.BhattScholze.Prismatic
