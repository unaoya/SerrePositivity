module

public import SerrePositivity.CommutativeAlgebra.PerfectoidizationFunctor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Module
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# perfectoid 化の環としての excision（文献入力）

## 概要
Bhatt–Scholze, *Prisms and prismatic cohomology*, Corollary 8.12（著者版 p.69）の
環としての引き戻しの帰結を引用する。
出典：https://people.mpim-bonn.mpg.de/scholze/prisms.pdf 。
手元の対応する原典は `paper/refs/BS-prisms-author.pdf` である。

## 方針
原典の E∞-S 代数の引き戻しから、Lemma 8.4（pp.63–64）の coconnectivity と
Proposition 8.5（pp.64–65）の導来極限表示を用いて H⁰ の環の引き戻しを得る帰結を引用する。
この導出自体は Lean では証明しない。

## 規約
四つの環としての普遍 perfectoid 化を明示的に受け取り、誘導射は既存の
`IsPerfectoidization.map` に固定する。導来対象・E∞ 構造・arc 位相は新設せず、
普遍環を持たない入力は扱わない。差写像の全射性は引用範囲に含めない。

## 使われ方
CLMST-D と KL-T が、指定された同じ環・標準誘導射の引き戻しを使うための名前付き引用である。
このファイルの一つの sorry はユーザー指定の文献入力であり、証明済みとは数えない。
-/

public section
universe u
namespace SerrePositivity.BhattScholze.Inputs
open CategoryTheory SerrePositivity.DerivedCompletion

/--
## 概要
BS Corollary 8.12（著者版 p.69）の環としての帰結。
R は perfectoid、S → T は導来 p 完備な R 代数の射、I ⊂ S は導来 p 完備イデアルで、
p 完備な階数 1 の付値環 V への S → V が I を消さないとき T → V へ一意に延びる、と仮定する。
S、T、S/I、T/IT の環としての普遍 perfectoid 化が与えられれば、誘導される環の四角形は引き戻しである。

## 方針
原典の結論は E∞-S 代数（特に D(S)）の引き戻しである。環の引き戻しはその H⁰ であり、
次の三点から従う。(1) Cor 8.12 の引き戻しが与える差写像のファイバー列の長完全列、
(2) Lemma 8.4（pp.63–64）により各 perfectoid 化は D^{≥0} に入るので H⁻¹ 項が消えること、
(3) Prop 8.5（pp.64–65）により導来 perfectoid 化は perfectoid 環への全写像にわたる導来極限で、
その H⁰ は通常の極限、普遍環が存在すればそれが始対象なので極限はその環に一致し、
誘導射は普遍性による射に一致すること。この導出を含む環としての帰結をここでは引用する。

## 規約
導来対象・E∞ 構造・arc 位相はここでは定義せず、普遍環を持たない入力は扱わない。
原典が与える差写像の全射性は引用しない。
出典：https://people.mpim-bonn.mpg.de/scholze/prisms.pdf（Corollary 8.12、p.69）。

## 使われ方
四つの指定された普遍環の標準誘導射について、CLMST-D と KL-T へ引き戻しを渡す。
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
  sorry

end SerrePositivity.BhattScholze.Inputs
