module

public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatEquiv
public import SerrePositivity.BhattScholze.Andre.Transfinite.Composition

/-!
# André E1・E2：根付き拡大の基底環同型による移送

## 概要

環同型は任意イデアルに関して完全忠実平坦であり、根付き p 完全忠実平坦拡大を
同じ宇宙の同型な基底環へ移せる。BS Thm 7.14（著者版 p.61）の構成の基底表示の比較。

## 方針

基底自身の完全忠実平坦性を線形同型で移し、既存の環射の合成定理を使う。
根方程式には多項式 map と eval₂ の自然性を用いる。
原典の Prop 7.11 による証明とは異なる、Rem 7.15（p.62）に沿う構成の補助計算。

## 規約

環射の作用は全て toAlgebra で固定する。元と終域の台環は同じ Type u に置く。

## 使われ方

完全 prism 商上の結果を、その商表示を持つ元の perfectoid 基底へ移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open scoped TensorProduct
variable {R S T σ : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- 概要：基底自身は任意イデアルに関して完全忠実平坦。
方針：高次 Tor の消滅と剰余テンソルの右単位同型を使う。
規約：通常の自己スカラー作用を使う。
使われ方：BS Thm 7.14（著者版 p.61）の基底環同型への移送。 -/
theorem monicRootedBase_self_isCompletelyFaithfullyFlat (I : Ideal R) :
    IsCompletelyFaithfullyFlat I R := by
  constructor
  · intro N _ _ _
    apply (isConcentratedInDegreeZero_derivedTensor_iff R N).mpr
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact torModule_subsingleton_of_flat R N m
  · exact Module.FaithfullyFlat.of_linearEquiv (R ⧸ I) (R ⧸ I)
      (TensorProduct.AlgebraTensorModule.rid R (R ⧸ I) (R ⧸ I))

/-- 概要：環同型は任意イデアルに関して完全忠実平坦。
方針：環同型を元の環上の線形同型とみなし、自己拡大の性質を移す。
規約：終域の係数作用は同型の toAlgebra に固定する。
使われ方：BS Rem 7.15（著者版 p.62）の具体的商表示からの移送。 -/
theorem monicRootedBase_equiv_isCompletelyFaithfullyFlat (e : R ≃+* S) (I : Ideal R) :
    letI := e.toRingHom.toAlgebra
    IsCompletelyFaithfullyFlat I S := by
  let := e.toRingHom.toAlgebra
  let E : R ≃ₗ[R] S :=
    { e.toAddEquiv with
      map_smul' := by
        intro a x
        change e (a * x) = e a * e x
        exact e.map_mul a x }
  exact isCompletelyFaithfullyFlat_of_linearEquiv I E
    (monicRootedBase_self_isCompletelyFaithfullyFlat I)

/-- 概要：同型先の基底の根付き p 完全忠実平坦拡大は元の基底の拡大でもある。
方針：同型の完全忠実平坦性と環射の合成定理を使い、eval₂_map で根方程式を移す。
規約：多項式族の性質や有限性はこの移送には不要。
使われ方：BS Thm 7.14（著者版 p.61）、Rem 7.15（p.62）の基底表示の解消。 -/
theorem monicRootedExtension_of_baseEquiv (p : ℕ) [Fact p.Prime]
    (e : R ≃+* S) (f : σ → Polynomial R) (g : S →+* T) (ρ : σ → T)
    (hT : IsIntegralPerfectoid T p)
    (hflat : letI := g.toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : S)}) T)
    (hroot : ∀ s, ((f s).map e.toRingHom).eval₂ g (ρ s) = 0) :
    IsIntegralPerfectoid T p ∧
      (letI := (g.comp e.toRingHom).toAlgebra;
        IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ (g.comp e.toRingHom) (ρ s) = 0 := by
  refine ⟨hT, ?_, ?_⟩
  · exact Transfinite.isCompletelyFaithfullyFlat_natCast_comp e.toRingHom g p
      (monicRootedBase_equiv_isCompletelyFaithfullyFlat e _) hflat
  · intro s
    simpa only [Polynomial.eval₂_map] using hroot s

end SerrePositivity.BhattScholze.Andre
