module

public import SerrePositivity.BhattScholze.Inputs.PerfectoidizationInterface
public import SerrePositivity.BhattScholze.PerfectoidizationInterface.Excision
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationFunctor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Module
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

/-! # perfectoid 化の環としての excision（界面から導出した定理）

従来 BS Cor 8.12 の環としての帰結を直接引用していた公開入口である。
現在は E3 界面から指定錐の比較・離散性・長完全列を経て導く。
公開名・型と四つの指定普遍環・標準誘導射を保つので、CLMST の利用箇所は変更しない。
-/

public section
universe u
namespace SerrePositivity.BhattScholze.Inputs
open CategoryTheory SerrePositivity.DerivedCompletion

/--
## 概要
BS Cor 8.12（著者版 p.69）の環としての帰結を、E3 界面から導出した定理。

## 方針
界面の存在を取り出して Π2-7′ の定理へ渡す。Prop 8.5 の制限付き極限を
四つの指定普遍環の始対象性で計算し、導来対象全体の離散性を得る。
界面の D(R) の excision と D4・D6a の指定四辺の長完全列から、H⁰ の短完全列と
環の引き戻しを導く。単位の自然性と環の普遍性で元の四辺に同定する。

## 規約
この公開入口は以前 Cor 8.12 の文献入力であったが、現在は直接の未証明箇所を持たない。
根拠の照合は Lemma 8.4（pp.63–64）、Prop 8.5（pp.64–65）、Cor 8.11・8.12、
Cor 8.14（p.70）と `formalization-plans/perfectoidization-interface.md` §3・§6 に記録する。
原典：https://people.mpim-bonn.mpg.de/scholze/prisms.pdf 。
差写像の全射性は Π2 の定理として公開し、この Inputs の公開型には追加しない。

## 使われ方
同じ四つの環・単位・`IsPerfectoidization.map` の引き戻しを CLMST-D と KL-T に供給する。
-/
theorem perfectoidization_excision_isPullback
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (f : S →ₐ[R] T) (I : Ideal S)
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hI : IsModuleComplete S (p : S) (ModuleCat.of S I))
    (harc : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V],
      ringKrullDim V = 1 → IsAdicComplete (Ideal.span {(p : V)}) V →
      ∀ k : S →+* V, ¬ (I ≤ RingHom.ker k) → ∃! l : T →+* V, l.comp f.toRingHom = k)
    {C D Q E : Type u} [CommRing C] [CommRing D] [CommRing Q] [CommRing E]
    {ηS : S →+* C} {ηT : T →+* D} {ηQ : S ⧸ I →+* Q} {ηE : T ⧸ I.map f.toRingHom →+* E}
    (hC : IsPerfectoidization p ηS) (hD : IsPerfectoidization p ηT)
    (hQ : IsPerfectoidization p ηQ) (hE : IsPerfectoidization p ηE) :
    IsPullback
      (CommRingCat.ofHom (IsPerfectoidization.map hC hD f.toRingHom))
      (CommRingCat.ofHom (IsPerfectoidization.map hC hQ (Ideal.Quotient.mk I)))
      (CommRingCat.ofHom (IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom))))
      (CommRingCat.ofHom (IsPerfectoidization.map hQ hE
        (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map))) := by
  exact PerfectoidizationInterface.perfectoidization_excision_isPullback R S T p hR
    (Classical.choice (exists_perfectoidizationInterfaceE3 R p hR))
    f I hS hT hI harc hC hD hQ hE

end SerrePositivity.BhattScholze.Inputs
