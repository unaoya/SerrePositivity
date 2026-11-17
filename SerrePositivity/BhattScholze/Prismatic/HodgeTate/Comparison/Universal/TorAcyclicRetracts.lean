module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.TorAcyclicResolvedRows

/-!
# 元の係数拡大のTor消滅と実際の直和因子

## 概要
元の二本の分裂射により、Tor消滅を元の加群の直和因子へ移す。

## 方針
同じTor関手で分裂の等式を写し、零対象を経由する恒等射を零とする。

## 規約
直和因子であることを型だけから仮定せず、実際の射と合成の等式を要求する。

## 使われ方
元の完備形式の係数拡大を、検証済みの元の完備自由多項式行へ戻す。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
variable {A B : Type u} [CommRing A] [CommRing B]

/-- 元の係数拡大の高次Tor消滅は、実際に分裂した直和因子へ移る。 -/
theorem scalarExtensionTorVanishing_of_split (f : A →+* B)
    {M N : ModuleCat.{u} A} (i : M ⟶ N) (q : N ⟶ M) (h : i ≫ q = 𝟙 M)
    (hN : scalarExtensionTorVanishing f N) : scalarExtensionTorVanishing f M := by
  intro n hn
  let T := (Tor (ModuleCat.{u} A) n).obj (baseChangeScalarModule f)
  apply (IsZero.iff_id_eq_zero _).mpr
  have ht := congrArg T.map h
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at ht
  rw [(hN n hn).eq_of_tgt (T.map i) 0, zero_comp] at ht
  exact ht.symm

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
