module

public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.PerfectComplex.NormalizedLengthComap

/-! # 任意の塔上の長さを完備化へ制限する

`NormalizedLength` を引数に取り、p 進完備化上の加群を非完備な塔に制限して測る。
具体的な塔の長さの一致・加法性の引用はこのモジュールには含めない。
直接の係数制限と、完備化を経由する係数制限が同じ値を与えることを証明する。
-/

@[expose] public section
universe u
open CategoryTheory
open IsLocalRing
namespace SerrePositivity.Section2

variable (A : Type u) [CommRing A] [IsLocalRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 任意の塔上の正規化長さの、p 進完備化への係数制限。
塔上の長さは明示的な引数なので、具体的な加法性の引用に依存しない。 -/
noncomputable def completedLengthOf
    (L : NormalizedLength (Tower A t p) (towerMaxIdeal A t p)) :
    NormalizedLength (CompletedTower A t p) (completedTowerMaxIdeal A t p) :=
  L.comap (algebraMap (Tower A t p) (CompletedTower A t p)) _
    (towerMaxIdeal_map_completed A t p).le

/-- 直接の係数制限と、完備化を経由する係数制限の長さは一致する。
両立する代数作用から係数制限関手の合成同型を使い、L の同型不変性を適用する。 -/
theorem completedLengthOf_restrictScalars
    (L : NormalizedLength (Tower A t p) (towerMaxIdeal A t p))
    (C : Type u) [CommRing C] [Algebra (Tower A t p) C]
    [Algebra (CompletedTower A t p) C]
    [IsScalarTower (Tower A t p) (CompletedTower A t p) C]
    (M : Type u) [AddCommGroup M] [Module C M] :
    (letI := Module.compHom M (algebraMap (Tower A t p) C)
     L.len M) =
    (letI := Module.compHom M (algebraMap (CompletedTower A t p) C)
     (completedLengthOf A t p L).len M) := by
  exact L.len_congr
    ((ModuleCat.restrictScalars (algebraMap (Tower A t p) C)).obj (ModuleCat.of C M))
    ((ModuleCat.restrictScalars (algebraMap (Tower A t p) (CompletedTower A t p))).obj
      ((ModuleCat.restrictScalars (algebraMap (CompletedTower A t p) C)).obj
        (ModuleCat.of C M)))
    (ModuleCat.restrictScalarsComp'App
      (algebraMap (Tower A t p) (CompletedTower A t p))
      (algebraMap (CompletedTower A t p) C) (algebraMap (Tower A t p) C)
      (IsScalarTower.algebraMap_eq _ _ _) (ModuleCat.of C M)).toLinearEquiv

end SerrePositivity.Section2
