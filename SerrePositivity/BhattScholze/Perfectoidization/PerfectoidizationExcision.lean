module

public import SerrePositivity.BhattScholze.PerfectoidizationInterface.ArcExcision
public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidizationExcisionDiagram
public import SerrePositivity.CommutativeAlgebra.IntegralAwayExtension

/-!
# 指定された標準 perfectoid 化の excision 四角形

## 概要
BS 著者版 Corollary 8.12（印刷 p.69）の環の引用から、元の普遍単位と
B3 の閉側の単位を持つ標準四角形の引き戻しを導く。

## 方針
閉側の単位の普遍性を引用へ供給し、四辺を既存の実写像と同定する。
整写像が指定元を逆にした後に同型なら、共通の付値環への一意延長定理で引用の条件を満たす。

## 規約
CLMST は import しない。積分性は q 自身が定める A 代数構造に関する条件である。
本ファイルに sorry はなく、外部入力は既存 ArcExcision の一件だけである。

## 使われ方
CLMST-D と KL-T が元の perfectoid 化の標準 excision 四角形を使うための二つの系である。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/--
## 概要
付値環への一意延長条件の下で、指定された perfectoid 化と B3 の閉側による
標準 excision 四角形は引き戻しである（BS 著者版 Cor 8.12、印刷 p.69）。

## 方針
閉側の B3 単位の普遍性を ArcExcision の引用へ渡す。
左右辺は普遍性の一意性、底辺は既証の標準比較射の等式で同定する。

## 規約
A、B、指定主イデアルの導来 p 完備性を明示し、閉側を別のモデルへ置き換えない。

## 使われ方
CLMST の KLCanonicalExcisionSquare と定義上同じ命題を、CLMST の import なしに供給する。
-/
theorem klCanonicalExcisionSquare_of_excision
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (A B C D : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (q : A →ₐ[R] B) (a : R) (f : A →ₐ[R] C) (g : B →ₐ[R] D)
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom)
    (hA : IsModuleComplete A (p : A) (ModuleCat.of A A))
    (hB : IsModuleComplete B (p : B) (ModuleCat.of B B))
    (hI : IsModuleComplete A (p : A) (ModuleCat.of A (Ideal.span {algebraMap R A a})))
    (harc : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V],
      ringKrullDim V = 1 → IsAdicComplete (Ideal.span {(p : V)}) V →
      ∀ k : A →+* V, ¬ (Ideal.span {algebraMap R A a} ≤ RingHom.ker k) →
        ∃! l : B →+* V, l.comp q.toRingHom = k) :
    IsPullback
      (CommRingCat.ofHom (IsPerfectoidization.map hf hg q.toRingHom))
      (CommRingCat.ofHom (perfectoidizationClosedSideProjection hf
        (Ideal.span {algebraMap R A a})))
      (CommRingCat.ofHom (perfectoidizationClosedSideProjection hg
        ((Ideal.span {algebraMap R A a}).map q.toRingHom)))
      (CommRingCat.ofHom (perfectoidizationClosedComparison hf hg q.toRingHom
        (Ideal.span {algebraMap R A a}))) := by
  let I := Ideal.span {algebraMap R A a}
  have hQ := perfectoidizationClosedSideUnit_isPerfectoidization hf I
  have hE := perfectoidizationClosedSideUnit_isPerfectoidization hg (I.map q.toRingHom)
  have hPB := Inputs.perfectoidization_excision_isPullback R A B p hR q I
    hA hB hI harc hf hg hQ hE
  have hleft : perfectoidizationClosedSideProjection hf I =
      IsPerfectoidization.map hf hQ (Ideal.Quotient.mk I) :=
    IsPerfectoidization.lift_unique hf hQ.1 _ _
      (perfectoidizationClosedSideProjection_comp hf I)
  have hright : perfectoidizationClosedSideProjection hg (I.map q.toRingHom) =
      IsPerfectoidization.map hg hE (Ideal.Quotient.mk (I.map q.toRingHom)) :=
    IsPerfectoidization.lift_unique hg hE.1 _ _
      (perfectoidizationClosedSideProjection_comp hg (I.map q.toRingHom))
  rw [← hleft, ← hright, ← perfectoidizationClosedComparison_eq_map hf hg q.toRingHom I] at hPB
  exact hPB

/--
## 概要
整写像 q が指定元の外で同型なら、標準 perfectoid 化の excision 四角形は引き戻しである
（BS 著者版 Cor 8.12、印刷 p.69 の系）。

## 方針
主イデアルを消さない条件を生成元の像の非零性へ直し、共通の整拡大・局所化からの
付値環への一意延長定理を適用して、付値環条件を持つ系へ渡す。

## 規約
積分性の A 代数構造は q.toRingHom.toAlgebra に固定する。別の A 作用の積分性で代用しない。
有限性・単射性・付値環への追加条件は仮定しない。

## 使われ方
CLMST-D と KL-T へ、元の q、a、f、g に関する標準四角形の引き戻しを供給する。
-/
theorem klCanonicalExcisionSquare_of_integral_away
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (A B C D : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (q : A →ₐ[R] B) [hInt : @Algebra.IsIntegral A B _ _ q.toRingHom.toAlgebra]
    (a : R) (f : A →ₐ[R] C) (g : B →ₐ[R] D)
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom)
    (hA : IsModuleComplete A (p : A) (ModuleCat.of A A))
    (hB : IsModuleComplete B (p : B) (ModuleCat.of B B))
    (hI : IsModuleComplete A (p : A) (ModuleCat.of A (Ideal.span {algebraMap R A a})))
    (haway : Function.Bijective (Localization.awayMap q.toRingHom (algebraMap R A a))) :
    IsPullback
      (CommRingCat.ofHom (IsPerfectoidization.map hf hg q.toRingHom))
      (CommRingCat.ofHom (perfectoidizationClosedSideProjection hf
        (Ideal.span {algebraMap R A a})))
      (CommRingCat.ofHom (perfectoidizationClosedSideProjection hg
        ((Ideal.span {algebraMap R A a}).map q.toRingHom)))
      (CommRingCat.ofHom (perfectoidizationClosedComparison hf hg q.toRingHom
        (Ideal.span {algebraMap R A a}))) := by
  apply klCanonicalExcisionSquare_of_excision R p hR A B C D q a f g hf hg hA hB hI
  intro V _ _ _ _ _ k hk
  have hiff : ¬ (Ideal.span {algebraMap R A a} ≤ RingHom.ker k) ↔
      k (algebraMap R A a) ≠ 0 := by
    rw [Ideal.span_singleton_le_iff_mem]
    rfl
  let : Algebra A B := q.toRingHom.toAlgebra
  let : Algebra A V := k.toAlgebra
  exact existsUnique_valuation_extension_of_integral_away_bijective A B V
    (algebraMap R A a) (hiff.mp hk) haway

end SerrePositivity.BhattScholze
