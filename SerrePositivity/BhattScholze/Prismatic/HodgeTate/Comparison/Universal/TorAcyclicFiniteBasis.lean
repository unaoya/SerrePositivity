module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.TorAcyclicRetracts
public import SerrePositivity.HomologicalAlgebra.Resolution
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# 元の有限自由加群へのTor消滅の移行

## 概要
係数代数の台加群のTor消滅を、その係数代数上の元の有限基底を持つ加群へ移す。

## 方針
元の座標射と基底ベクトルの射の合成和を恒等射と書き、同じ加法的Tor関手で写す。

## 規約
元の基底作用への係数制限を使う。基底環の通常の平坦性は仮定しない。

## 使われ方
元の完備形式のsingleの被覆への導来係数拡大を計算する。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- 係数代数の元の台加群のTor消滅は、元の有限基底を持つ加群へ移る。 -/
theorem scalarExtensionTorVanishing_of_finiteBasis (f : A →+* B) (g : A →+* C)
    (hC : scalarExtensionTorVanishing f ((ModuleCat.restrictScalars g).obj (ModuleCat.of C C)))
    {I : Type u} [Fintype I] (M : ModuleCat.{u} C) (b : Module.Basis I C M) :
    scalarExtensionTorVanishing f ((ModuleCat.restrictScalars g).obj M) := by
  let U := ModuleCat.restrictScalars g
  let i : I → (ModuleCat.of C C ⟶ M) := fun j =>
    ModuleCat.ofHom ((LinearMap.id : C →ₗ[C] C).smulRight (b j))
  let q : I → (M ⟶ ModuleCat.of C C) := fun j => ModuleCat.ofHom (b.coord j)
  have hb : (∑ j, q j ≫ i j) = 𝟙 M := by
    apply ModuleCat.hom_ext
    ext x
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
      ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply]
    change (∑ j, (b.repr x j) • b j) = x
    exact b.sum_repr x
  intro n hn
  let T := (Tor (ModuleCat.{u} A) n).obj (baseChangeScalarModule f)
  apply (IsZero.iff_id_eq_zero _).mpr
  haveI : T.Additive := by
    change (((MonoidalCategory.tensoringLeft (ModuleCat.{u} A)).obj
      (baseChangeScalarModule f)).leftDerived n).Additive
    infer_instance
  let V := U ⋙ T
  have ht := congrArg V.map hb
  rw [V.map_sum, CategoryTheory.Functor.map_id] at ht
  have hq (j : I) : T.map (U.map (q j)) = 0 := (hC n hn).eq_of_tgt _ _
  have hz (j : I) : V.map (q j ≫ i j) = 0 := by
    change T.map (U.map (q j ≫ i j)) = 0
    rw [U.map_comp, T.map_comp, hq, zero_comp]
  simp only [hz, Finset.sum_const_zero] at ht
  exact ht.symm

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
