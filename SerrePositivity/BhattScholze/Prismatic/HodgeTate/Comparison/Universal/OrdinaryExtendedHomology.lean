module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.OrdinaryExtendedUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.MapExtendHomologyCompatibility
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.HomologyUnitComposite

/-!
# 元の零延長の通常ホモロジー比較の評価

## 概要
元の非負余鎖の単位の正方形は、同じ指定された零延長のホモロジー座標でも保たれる。

## 方針
随伴単位からの純テンソル評価と、係数制限・零延長の元のホモロジー同型の整合性を使う。

## 規約
通常係数拡大によるホモロジー保存は仮定しない。

## 使われ方
元のHT実現の被覆像を、同じ元の剰余係数射のコホモロジー類で計算する。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
open scoped TensorProduct ChangeOfRings
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HTComparisonTotal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の零延長後の通常比較の純テンソルは、元の非負余鎖射のホモロジー写像を与える。 -/
theorem ordinaryExtendedHomology_one_tmul (f : R →+* S)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (L : CochainComplex (ModuleCat.{u} S) ℕ)
    (g : ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℕ)).obj K ⟶ L)
    (h : K ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℕ)).obj L)
    (hu : ∀ n, (ModuleCat.extendRestrictScalarsAdj f).unit.app (K.X n) ≫
      (ModuleCat.restrictScalars f).map (g.f n) = h.f n)
    (n : ℕ) (x : K.homology n) :
    (L.extendHomologyIso ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).hom
      (homologyMap ((SerrePositivity.mapExtendIso (ModuleCat.extendScalars f) K
          ComplexShape.embeddingUpNat).hom ≫ extendMap g ComplexShape.embeddingUpNat) (n : ℤ)
        (complexBaseChangeHomologyComparison f (K.extend ComplexShape.embeddingUpNat) (n : ℤ)
          ((1 : S) ⊗ₜ[R,f] (K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).inv x))) =
      ((L.sc n).mapHomologyIso (ModuleCat.restrictScalars f)).hom (homologyMap h n x) := by
  let U := ModuleCat.restrictScalars f
  let e := ComplexShape.embeddingUpNat
  let LU := (U.mapHomologicalComplex (.up ℕ)).obj L
  let γ := SerrePositivity.mapExtendIso U L e
  let h' := extendMap h e ≫ γ.inv
  let g' := (SerrePositivity.mapExtendIso (ModuleCat.extendScalars f) K e).hom ≫ extendMap g e
  have hc := mapExtendIso_homology_compatibility U L n
  have hc' : homologyMap γ.inv (n : ℤ) ≫
      (((L.extend e).sc (n : ℤ)).mapHomologyIso U).hom ≫
      U.map (L.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).hom =
    (LU.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).hom ≫ ((L.sc n).mapHomologyIso U).hom := by
    erw [← hc, ← Category.assoc, ← homologyMap_comp,
      Iso.inv_hom_id, homologyMap_id, Category.id_comp]
  have hh : homologyMap h' (n : ℤ) ≫
      (((L.extend e).sc (n : ℤ)).mapHomologyIso U).hom ≫
      U.map (L.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).hom =
    (K.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).hom ≫ homologyMap h n ≫
      ((L.sc n).mapHomologyIso U).hom := by
    dsimp only [h']
    erw [homologyMap_comp, Category.assoc, hc', ← Category.assoc,
      extendHomologyIso_hom_naturality]
    simp only [Category.assoc]
  have hv := complexBaseChangeHomologyComparison_one_tmul_comp f (K.extend e) (L.extend e)
    g' h' (ordinaryExtendedUnit f K L g h hu) (n : ℤ)
    ((K.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).inv x)
  have hv' := congrArg (fun z => (L.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).hom z) hv
  have hp := ConcreteCategory.congr_hom hh ((K.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).inv x)
  change (L.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).hom
      ((((L.extend e).sc (n : ℤ)).mapHomologyIso U).hom
        (homologyMap h' (n : ℤ) ((K.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).inv x))) =
    ((L.sc n).mapHomologyIso U).hom
      (homologyMap h n ((K.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).hom
        ((K.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).inv x))) at hp
  rw [ModuleCat.hom_inv_apply] at hp
  exact hv'.trans hp

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
