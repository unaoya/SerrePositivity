module

public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Cover
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Excision
public import SerrePositivity.CommutativeAlgebra.Localization.Away

/-!
# perfectoid 化の環としての excision の帰結（BS 著者版 Corollary 8.12 の環版の適用）

## 概要
excision 図式の四つの普遍環と標準射、CLMST の KL 標準 excision 四角形への接続（整で a の外で同型な場合を含む）。

## 方針
BS 著者版 Corollary 8.12 の環版（PerfectoidizationInterface/Excision）を図式に当てる。

## 規約
BS 著者版 Corollary 8.12 自体は E3 から導いた定理。

## 使われ方
CLMST。
-/

universe u

/-! ## The actual four universal maps of an excision diagram

The closed sides are chosen by B3 from quotients of the specified perfectoid
rings. Their units are universal for the original source quotients as well.
Only commutativity and identification of these actual maps are proved here;
no excision or pullback assertion is added as an input or inferred.
-/

@[expose] public noncomputable section PerfectoidizationExcisionDiagram

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    {p : ℕ} [Fact p.Prime] {f : A →+* C} {g : B →+* D}

/-- The closed-side unit from the original source quotient. -/
def perfectoidizationClosedSideUnit (hf : IsPerfectoidization p f) (J : Ideal A) :
    A ⧸ J →+* QuotientPerfectoidization C (J.map f) p hf.1 :=
  (toQuotientPerfectoidization C (J.map f) p hf.1).comp
    (Ideal.quotientMap (J.map f) f Ideal.le_comap_map)

/-- This exact unit is universal for the original source quotient. -/
theorem perfectoidizationClosedSideUnit_isPerfectoidization
    (hf : IsPerfectoidization p f) (J : Ideal A) :
    IsPerfectoidization p (perfectoidizationClosedSideUnit hf J) :=
  hf.quotient_map J (toQuotientPerfectoidization C (J.map f) p hf.1)
    (isPerfectoidization_toQuotientPerfectoidization C (J.map f) p hf.1)

/-- The vertical map starts at the specified perfectoid ring, not at a replacement model. -/
def perfectoidizationClosedSideProjection (hf : IsPerfectoidization p f) (J : Ideal A) :
    C →+* QuotientPerfectoidization C (J.map f) p hf.1 :=
  (toQuotientPerfectoidization C (J.map f) p hf.1).comp (Ideal.Quotient.mk (J.map f))

/-- The original unit square commutes on the entire source ring. -/
theorem perfectoidizationClosedSideProjection_comp
    (hf : IsPerfectoidization p f) (J : Ideal A) :
    (perfectoidizationClosedSideProjection hf J).comp f =
      (perfectoidizationClosedSideUnit hf J).comp (Ideal.Quotient.mk J) := rfl

/-- The vertical map kills the images of all original members of the ideal. -/
theorem perfectoidizationClosedSideProjection_eq_zero_of_mem
    (hf : IsPerfectoidization p f) (J : Ideal A) (x : A) (hx : x ∈ J) :
    perfectoidizationClosedSideProjection hf J (f x) = 0 := by
  change toQuotientPerfectoidization C (J.map f) p hf.1
    (Ideal.Quotient.mk (J.map f) (f x)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f hx), map_zero]

/-- The original base perfectoid ideal is killed on the closed side, through
exactly the original coefficient map and the original quotient unit. -/
theorem perfectoidizationClosedSideProjection_originalIdeal
    {R : Type u} [CommRing R] (hR : IsIntegralPerfectoid R p) (α : R →+* A)
    (hf : IsPerfectoidization p f) (J : Ideal A) (a : R) (ha : α a ∈ J) :
    ∀ s ∈ perfectoidIdeal R p hR a,
      perfectoidizationClosedSideProjection hf J (f (α s)) = 0 := by
  let k := (perfectoidizationClosedSideProjection hf J).comp (f.comp α)
  have hk : k a = 0 := perfectoidizationClosedSideProjection_eq_zero_of_mem hf J (α a) ha
  exact perfectoidIdeal_le_ker_of_eq_zero R p hR
    (isPerfectoidization_toQuotientPerfectoidization C (J.map f) p hf.1).1 k a hk

/-- The actual functorial top map sends the original closed-side ideal into its image. -/
theorem perfectoidizationClosedComparison_ideal_le
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (J : Ideal A) :
    J.map f ≤ ((J.map q).map g).comap (IsPerfectoidization.map hf hg q) := by
  apply Ideal.map_le_iff_le_comap.mp
  rw [Ideal.map_map, hf.map_comp hg q, ← Ideal.map_map]

/-- The lower horizontal map between the actual B3 closed-side objects. -/
def perfectoidizationClosedComparison
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (J : Ideal A) :
    QuotientPerfectoidization C (J.map f) p hf.1 →+*
      QuotientPerfectoidization D ((J.map q).map g) p hg.1 :=
  quotientPerfectoidizationMap p hf.1 hg.1 (IsPerfectoidization.map hf hg q)
    (J.map f) ((J.map q).map g) (perfectoidizationClosedComparison_ideal_le hf hg q J)

/-- The actual perfectoidization excision square commutes. This is not a pullback assertion. -/
theorem perfectoidizationClosedComparison_square
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (J : Ideal A) :
    (perfectoidizationClosedComparison hf hg q J).comp
        (perfectoidizationClosedSideProjection hf J) =
      (perfectoidizationClosedSideProjection hg (J.map q)).comp
        (IsPerfectoidization.map hf hg q) := by
  ext x
  exact quotientPerfectoidizationMap_mk p hf.1 hg.1 (IsPerfectoidization.map hf hg q)
    (J.map f) ((J.map q).map g) (perfectoidizationClosedComparison_ideal_le hf hg q J) x

/-- The lower horizontal map retains the original quotient units and quotient map. -/
theorem perfectoidizationClosedComparison_unit
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (J : Ideal A) :
    (perfectoidizationClosedComparison hf hg q J).comp
        (perfectoidizationClosedSideUnit hf J) =
      (perfectoidizationClosedSideUnit hg (J.map q)).comp
        (Ideal.quotientMap (J.map q) q Ideal.le_comap_map) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  have hs := RingHom.congr_fun (perfectoidizationClosedComparison_square hf hg q J) (f x)
  have hm : IsPerfectoidization.map hf hg q (f x) = g (q x) :=
    RingHom.congr_fun (hf.map_comp hg q) x
  change perfectoidizationClosedComparison hf hg q J
      (perfectoidizationClosedSideProjection hf J (f x)) =
    perfectoidizationClosedSideProjection hg (J.map q) (g (q x))
  change perfectoidizationClosedComparison hf hg q J
      (perfectoidizationClosedSideProjection hf J (f x)) =
    perfectoidizationClosedSideProjection hg (J.map q)
      (IsPerfectoidization.map hf hg q (f x)) at hs
  rw [hm] at hs
  exact hs

/-- The constructed lower map is precisely the functorial map for the original quotients. -/
theorem perfectoidizationClosedComparison_eq_map
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (J : Ideal A) :
    perfectoidizationClosedComparison hf hg q J =
      IsPerfectoidization.map (perfectoidizationClosedSideUnit_isPerfectoidization hf J)
        (perfectoidizationClosedSideUnit_isPerfectoidization hg (J.map q))
        (Ideal.quotientMap (J.map q) q Ideal.le_comap_map) :=
  IsPerfectoidization.lift_unique (perfectoidizationClosedSideUnit_isPerfectoidization hf J)
    (perfectoidizationClosedSideUnit_isPerfectoidization hg (J.map q)).1 _ _
    (perfectoidizationClosedComparison_unit hf hg q J)

end SerrePositivity.BhattScholze

end PerfectoidizationExcisionDiagram

/-! ## 指定された標準 perfectoid 化の excision 四角形

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

@[expose] public noncomputable section PerfectoidizationExcision

namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/--
## 概要
付値環への一意延長条件の下で、指定された perfectoid 化と B3 の閉側による
標準 excision 四角形は引き戻しである（BS 著者版 Corollary 8.12、印刷 p.69）。

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
（BS 著者版 Corollary 8.12、印刷 p.69 の系）。

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

end PerfectoidizationExcision

/-! ## 環の excision の引用とその二つの系の集約

## 概要
BS 著者版 Corollary 8.12（印刷 p.69）の環の引用と、標準閉側四角形に関する二つの系を公開する。
## 方針
既存の引用モジュールと、その引用だけから導いた系のモジュールを読み込む。
## 規約
引用入力は ArcExcision の一件であり、系の証明に新しい引用を追加しない。
## 使われ方
ルートの一行の import と、CLMST-D・KL-T への公開入口に使う。
-/
