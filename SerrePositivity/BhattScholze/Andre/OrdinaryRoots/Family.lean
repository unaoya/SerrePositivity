module
public import SerrePositivity.CommutativeAlgebra.Polynomial.MonicRelation
public import SerrePositivity.CommutativeAlgebra.Polynomial.IndependentMonicQuotient

public import SerrePositivity.BhattScholze.Andre.OrdinaryRoots.Adjoin
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Data.Fintype.Option
public import SerrePositivity.BhattScholze.Andre.Transfinite.Colimit

/-!
# モニック族の通常の根商：有限部分族の余極限と忠実平坦性

## 概要
任意個の正次数モニック多項式に独立な根を添加した商を、有限部分族の商の有向余極限として表し、普遍性・再添字付け・一変数の追加・部分族による商・係数商との交換を示す。有限族の商は自由、任意族の商は忠実平坦。
BS 著者版 Theorem 7.14 の根付き拡大に向けて、通常のモニック根商を有限部分族から構成する。

## 方針
有限族は帰納法で自由基底を作り、任意族は `Transfinite/Colimit` の忠実平坦性の余極限保存に渡す。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/MonicSource`、MonicRelationRegularSequence、`Variants/Auxiliary`、`Variants/MonicRootedExtension`、`Variants/RootedExtension`。
-/

universe u v w

/-! ## 独立な多項式関係の部分族による商

## 概要

先行変数だけの任意多項式関係で割った環は、その関係の商を係数とする残りの変数の
多項式環となる。残りの変数のモニック関係はこの商でも非零因子である。
BS 著者版 Corollary 2.39（p.25）、BS 著者版 Remark 7.15(1)（p.62）の有限独立関係族への準備。

## 方針

変数の直和分割と、係数商と多変数多項式環の交換同型を使う。
既存 B4-6 の冪根関係に固有な表示を使わず、先行多項式を任意に取る。

## 規約

先行関係にはモニック性・正次数・有限性を要求しない。
正則性を主張する残りの関係についてだけモニック性を要求する。
この商表示だけでは元の係数環上の忠実平坦性を結論しない。

## 使われ方

モニック族とその冪の先行商での正則性、および raw δ 除算の有限族入力に用いる。
-/

@[expose] public noncomputable section MonicFamilySubsetRegular

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {R : Type u} [CommRing R] {σ : Type v}

/-- 概要：先行関係で割った環は先行関係商上の補集合の多項式環。
方針：添字分割の商同型と直和版の商表示を合成する。
規約：先行関係の正則性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の独立変数族の通常代数。 -/
def polynomialSubsetQuotientEquiv (T : Set σ) (f : σ → Polynomial R) :
    (MvPolynomial σ R ⧸ polynomialSubsetRelationIdeal T f) ≃+*
      MvPolynomial (Tᶜ : Set σ)
        (MvPolynomial T R ⧸ polynomialFamilyRelationIdeal (fun s : T => f s)) :=
  (Ideal.quotientEquiv _ _
    (MvPolynomial.renameEquiv R (polynomialSubsetIndexEquiv T)).toRingEquiv
    (polynomialSubsetRelationIdeal_map_rename T f).symm).trans
      (partialPolynomialQuotientEquiv
        (Sum.elim (fun s : (Tᶜ : Set σ) => f s) (fun s : T => f s)))

end SerrePositivity.BhattScholze.Andre

end MonicFamilySubsetRegular

/-! ## 通常の多項式根族商の普遍性

## 概要

独立変数ごとの多項式関係の商における根方程式と、指定根を持つ任意の環への普遍射を構成する。
BS 著者版 Theorem 7.14（p.61）、BS 著者版 Remark 7.15（p.62）の通常モニック根添加の準備である。

## 方針

多変数多項式環の評価射を関係イデアルで降下させる。
係数と根上の公式を明示し、変数一つ追加の商と AdjoinRoot の比較に使う。

## 規約

この普遍性にはモニック性や正次数を要求しない。
商の自由性・忠実平坦性は別の結果であり、この普遍性だけからは結論しない。

## 使われ方

有限モニック族の通常商を一元根添加の反復と同定し、任意族の遷移射を固定する。
-/

@[expose] public noncomputable section MonicFamilyQuotientUniversal

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {R : Type u} [CommRing R] {σ : Type v}

/-- 概要：独立な多項式関係をすべて課した通常の根族商。
方針：既存の関係イデアルで多変数多項式環を割る。
規約：零商も許す。モニック性は定義に含めない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の通常根添加環。 -/
abbrev PolynomialFamilyQuotient (f : σ → Polynomial R) :=
  MvPolynomial σ R ⧸ polynomialFamilyRelationIdeal f

/-- 概要：各関係の指定根は変数の標準商像である。
方針：対応する変数を関係商へ写す。
規約：係数作用は通常の R 代数作用に固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根方程式を明示する。 -/
def polynomialFamilyQuotientRoot (f : σ → Polynomial R) (s : σ) :
    PolynomialFamilyQuotient f :=
  Ideal.Quotient.mk _ (MvPolynomial.X s)

/-- 概要：通常の根族商の標準根は元の多項式の根となる。
方針：評価の自然性と関係イデアルの生成元の消滅を使う。
規約：元の係数環の代数作用に関して述べる。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の通常根族の構成。 -/
theorem polynomialFamilyQuotient_eval (f : σ → Polynomial R) (s : σ) :
    (f s).eval₂ (algebraMap R (PolynomialFamilyQuotient f))
      (polynomialFamilyQuotientRoot f s) = 0 := by
  let q := Ideal.Quotient.mk (polynomialFamilyRelationIdeal f)
  change (f s).eval₂ (q.comp MvPolynomial.C) (q (MvPolynomial.X s)) = 0
  rw [← Polynomial.hom_eval₂]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self s))

/-- 概要：指定された根を持つ任意の環へ根族商からの実環射を構成する。
方針：多変数評価射が関係生成元を消すことから商に降下する。
規約：任意の係数環射と根族を指定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の一変数追加と商の比較。 -/
def polynomialFamilyQuotientLift {S : Type w} [CommRing S]
    (f : σ → Polynomial R) (φ : R →+* S) (a : σ → S)
    (ha : ∀ s, (f s).eval₂ φ (a s) = 0) : PolynomialFamilyQuotient f →+* S := by
  apply Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom φ a)
  change polynomialFamilyRelationIdeal f ≤ RingHom.ker (MvPolynomial.eval₂Hom φ a)
  apply Ideal.span_le.mpr
  rintro _ ⟨s, rfl⟩
  change (MvPolynomial.eval₂Hom φ a) (monicRelation (f s) s) = 0
  unfold monicRelation
  rw [Polynomial.hom_eval₂]
  simpa using ha s

/-- 概要：普遍射は標準根を指定根へ送る。
方針：商射の代表元公式と多変数評価の変数公式を使う。
規約：指定された根方程式の証明は任意。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の根を保持する遷移。 -/
theorem polynomialFamilyQuotientLift_root {S : Type w} [CommRing S]
    (f : σ → Polynomial R) (φ : R →+* S) (a : σ → S)
    (ha : ∀ s, (f s).eval₂ φ (a s) = 0) (s : σ) :
    polynomialFamilyQuotientLift f φ a ha (polynomialFamilyQuotientRoot f s) = a s := by
  exact MvPolynomial.eval₂Hom_X' φ a s

/-- 概要：普遍射は元の係数射を延長する。
方針：商射の代表元公式と多変数評価の係数公式を使う。
規約：通常の R 代数構造に対する公式。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数作用を保つ。 -/
theorem polynomialFamilyQuotientLift_coeff {S : Type w} [CommRing S]
    (f : σ → Polynomial R) (φ : R →+* S) (a : σ → S)
    (ha : ∀ s, (f s).eval₂ φ (a s) = 0) (x : R) :
    polynomialFamilyQuotientLift f φ a ha (algebraMap R (PolynomialFamilyQuotient f) x) =
      φ x := by
  exact MvPolynomial.eval₂Hom_C φ a x

/-- 概要：根族商からの環射は係数と標準根上の値で一意に決まる。
方針：商射と多変数多項式環の生成元に関する外延性を使う。
規約：標的に通常の環構造だけを要求する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の商表示の相互逆性。 -/
theorem polynomialFamilyQuotientHom_ext {S : Type w} [CommRing S]
    (f : σ → Polynomial R) (F G : PolynomialFamilyQuotient f →+* S)
    (hc : ∀ x : R, F (algebraMap R _ x) = G (algebraMap R _ x))
    (hx : ∀ s, F (polynomialFamilyQuotientRoot f s) =
      G (polynomialFamilyQuotientRoot f s)) : F = G := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · exact hc
  · exact hx

end SerrePositivity.BhattScholze.Andre

end MonicFamilyQuotientUniversal

/-! ## 通常根族商の有限部分族有向系

## 概要

任意の多項式族の有限部分族の通常商と、包含に沿う根を保つ標準遷移射を構成する。
BS 著者版 Theorem 7.14（p.61）、BS 著者版 Remark 7.15（p.62）の任意族の通常根添加の準備。

## 方針

各有限商の普遍射を用い、係数と標準根上で恒等性・合成則を確認する。
Mathlib の R 代数有向系として構成し、余極限で元の係数作用を保持する。

## 規約

モニック性・正次数はこの有向系の構成には不要。
遷移射の単射性や完備性も仮定しない。

## 使われ方

全族の通常商と有限商余極限の比較、および通常忠実平坦性の有限部分族からの移送。
-/

@[expose] public noncomputable section MonicFamilyFiniteSystem

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：標準係数作用の根族商から指定根を持つ R 代数への普遍代数射。
方針：既存の普遍環射に係数を保つ性質を付ける。
規約：指定根方程式だけを要求する。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の通常有限商の遷移射。 -/
def polynomialFamilyQuotientLiftAlgHom {R : Type u} [CommRing R] {σ : Type v}
    {S : Type w} [CommRing S] [Algebra R S] (f : σ → Polynomial R) (a : σ → S)
    (ha : ∀ s, (f s).eval₂ (algebraMap R S) (a s) = 0) :
    PolynomialFamilyQuotient f →ₐ[R] S :=
  { polynomialFamilyQuotientLift f (algebraMap R S) a ha with
    commutes' := polynomialFamilyQuotientLift_coeff f _ a ha }

/-- 概要：根族商からの代数射は標準根上の値で一意に決まる。
方針：係数上の一致は代数射性から供給し、環射の外延性を適用する。
規約：元の R 係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の遷移射の合成則の検証。 -/
theorem polynomialFamilyQuotientAlgHom_ext {R : Type u} [CommRing R] {σ : Type v}
    {S : Type w} [CommRing S] [Algebra R S] (f : σ → Polynomial R)
    (F G : PolynomialFamilyQuotient f →ₐ[R] S)
    (hx : ∀ s, F (polynomialFamilyQuotientRoot f s) = G (polynomialFamilyQuotientRoot f s)) :
    F = G := by
  apply AlgHom.toRingHom_injective
  apply polynomialFamilyQuotientHom_ext f
  · intro x
    exact (F.commutes x).trans (G.commutes x).symm
  · exact hx

variable {R : Type u} [CommRing R] {σ : Type v} (f : σ → Polynomial R)

/-- 概要：有限部分族に対応する通常の根族商。
方針：元の族を有限集合の部分型に制限する。
規約：同じ多項式族をすべての段で共有する。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の任意同時根添加の有限段。 -/
abbrev PolynomialFamilyFiniteStage (T : Finset σ) :=
  PolynomialFamilyQuotient (fun s : T => f s)

/-- 概要：有限部分族の包含は標準根を対応する標準根へ送る代数射を与える。
方針：商の普遍代数射に終域の標準根を指定する。
規約：係数作用を変えない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限部分族有向系。 -/
def polynomialFamilyFiniteMap {S T : Finset σ} (h : S ⊆ T) :
    PolynomialFamilyFiniteStage f S →ₐ[R] PolynomialFamilyFiniteStage f T :=
  polynomialFamilyQuotientLiftAlgHom (fun s : S => f s)
    (fun s => polynomialFamilyQuotientRoot (fun t : T => f t) ⟨s, h s.property⟩)
    (fun s => polynomialFamilyQuotient_eval (fun t : T => f t) ⟨s, h s.property⟩)

/-- 概要：有限部分族の遷移射は指定根を保持する。
方針：商の普遍射の根上の公式を適用する。
規約：包含の証明の違いは部分型の証明無関係性で吸収する。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の任意族の根の追跡。 -/
theorem polynomialFamilyFiniteMap_root {S T : Finset σ} (h : S ⊆ T) (s : S) :
    polynomialFamilyFiniteMap f h (polynomialFamilyQuotientRoot (fun t : S => f t) s) =
      polynomialFamilyQuotientRoot (fun t : T => f t) ⟨s, h s.property⟩ :=
  polynomialFamilyQuotientLift_root _ _ _
    (fun s : S => polynomialFamilyQuotient_eval (fun t : T => f t) ⟨s, h s.property⟩) s

/-- 概要：同じ有限部分族への恒等包含の遷移射は恒等代数射。
方針：標準根上の値を比較する。
規約：係数上の一致は代数射性による。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有向系の恒等則。 -/
theorem polynomialFamilyFiniteMap_self (T : Finset σ) :
    polynomialFamilyFiniteMap f (Finset.Subset.refl T) =
      AlgHom.id R (PolynomialFamilyFiniteStage f T) := by
  apply polynomialFamilyQuotientAlgHom_ext (fun t : T => f t)
  intro s
  rw [polynomialFamilyFiniteMap_root]
  rfl

/-- 概要：有限部分族の包含の合成は遷移代数射の合成に対応する。
方針：各標準根の行先が同じであることを示す。
規約：遷移射の単射性は使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有向系の合成則。 -/
theorem polynomialFamilyFiniteMap_comp {S T U : Finset σ} (h : S ⊆ T) (k : T ⊆ U) :
    (polynomialFamilyFiniteMap f k).comp (polynomialFamilyFiniteMap f h) =
      polynomialFamilyFiniteMap f (h.trans k) := by
  apply polynomialFamilyQuotientAlgHom_ext (fun s : S => f s)
  intro s
  change polynomialFamilyFiniteMap f k
    (polynomialFamilyFiniteMap f h (polynomialFamilyQuotientRoot (fun t : S => f t) s)) = _
  rw [polynomialFamilyFiniteMap_root, polynomialFamilyFiniteMap_root,
    polynomialFamilyFiniteMap_root]

/-- 概要：通常の有限部分族商と標準包含射は Mathlib の有向系をなす。
方針：恒等則と合成則を既存の有向系構造のフィールドへ渡す。
規約：全族の有限性を要求しない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の任意族の通常商の余極限。 -/
instance polynomialFamilyFiniteDirectedSystem :
    DirectedSystem (fun T : Finset σ => PolynomialFamilyFiniteStage f T)
      (fun _ _ h => polynomialFamilyFiniteMap f h) where
  map_self {i} x := by
    rw [polynomialFamilyFiniteMap_self]
    rfl
  map_map {k j i} hij hjk x :=
    DFunLike.congr_fun (polynomialFamilyFiniteMap_comp f hij hjk) x

/-- 概要：有限部分族の通常商から全族の通常商への標準代数射。
方針：全族の商の対応する標準根を普遍射に指定する。
規約：有限段と全族で同じ係数環を使う。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の全族商と余極限の比較。 -/
def polynomialFamilyFiniteToFull (T : Finset σ) :
    PolynomialFamilyFiniteStage f T →ₐ[R] PolynomialFamilyQuotient f :=
  polynomialFamilyQuotientLiftAlgHom (fun t : T => f t)
    (fun t => polynomialFamilyQuotientRoot f t) (fun t => polynomialFamilyQuotient_eval f t)

/-- 概要：有限段から全族商への標準射は根を保持する。
方針：商の普遍射の根公式を適用する。
規約：標準根の添字は元の添字への包含で比較する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全族の根の追跡。 -/
theorem polynomialFamilyFiniteToFull_root (T : Finset σ) (t : T) :
    polynomialFamilyFiniteToFull f T (polynomialFamilyQuotientRoot (fun s : T => f s) t) =
      polynomialFamilyQuotientRoot f t :=
  polynomialFamilyQuotientLift_root _ _ _ (fun s : T => polynomialFamilyQuotient_eval f s) t

/-- 概要：全族商への標準射は有限部分族の全遷移と両立する。
方針：標準根の値で両辺を比較する。
規約：有限部分族の包含は任意。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の余極限から全族商への標準射。 -/
theorem polynomialFamilyFiniteToFull_compatible {S T : Finset σ} (h : S ⊆ T) :
    (polynomialFamilyFiniteToFull f T).comp (polynomialFamilyFiniteMap f h) =
      polynomialFamilyFiniteToFull f S := by
  apply polynomialFamilyQuotientAlgHom_ext (fun s : S => f s)
  intro s
  change polynomialFamilyFiniteToFull f T
    (polynomialFamilyFiniteMap f h (polynomialFamilyQuotientRoot (fun t : S => f t) s)) = _
  rw [polynomialFamilyFiniteMap_root, polynomialFamilyFiniteToFull_root,
    polynomialFamilyFiniteToFull_root]

end SerrePositivity.BhattScholze.Andre

end MonicFamilyFiniteSystem

/-! ## 全族の通常根商と有限部分族の余極限

## 概要

任意多項式族の通常根商を有限部分族の通常商の R 代数余極限と同定する。
BS 著者版 Theorem 7.14（p.61）、BS 著者版 Remark 7.15（p.62）の任意同時根添加の通常代数部分である。

## 方針

各根を一元集合の段から余極限へ写し、根族商の普遍射を用いて逆射を作る。
有限段の生成元で両立性と相互逆性を確認する。

## 規約

モニック性・正次数・遷移射の単射性を仮定しない。
有向余極限の自由性はこの同型からは主張しない。

## 使われ方

有限モニック族の通常忠実平坦性を全族の実際の関係商へ移す。
-/

@[expose] public noncomputable section MonicFamilyColimit

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {R : Type u} [CommRing R] {σ : Type v} (f : σ → Polynomial R)

local notation "S" => (fun T : Finset σ => PolynomialFamilyFiniteStage f T)
local notation "d" => (fun (i : Finset σ) (j : Finset σ) (h : i ≤ j) =>
  polynomialFamilyFiniteMap f h)

/-- 概要：有限部分族の通常商の標準 R 代数余極限。
方針：前工程で構成した有向系に Mathlib の DirectLimit を適用する。
規約：元の係数作用を保持する。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の任意族の通常根添加。 -/
abbrev PolynomialFamilyColimit := _root_.DirectLimit S d

/-- 概要：各有限商から通常根族余極限への標準代数射。
方針：Mathlib の標準構造射を使う。
規約：遷移射と同じ R 係数作用。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限段からの根の像。 -/
def polynomialFamilyColimitOf (T : Finset σ) :
    PolynomialFamilyFiniteStage f T →ₐ[R] PolynomialFamilyColimit f :=
  DirectLimit.Algebra.of S d T

/-- 概要：余極限への構造射は有限段の遷移射と両立する。
方針：DirectLimit の構造射の関係式を使う。
規約：包含の単射性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根の段への依存を除く。 -/
theorem polynomialFamilyColimitOf_compatible {T U : Finset σ} (h : T ⊆ U)
    (x : PolynomialFamilyFiniteStage f T) :
    polynomialFamilyColimitOf f U (polynomialFamilyFiniteMap f h x) =
      polynomialFamilyColimitOf f T x :=
  DirectLimit.Algebra.of_f h x

/-- 概要：全族の各根をその一元部分族から余極限に入れる。
方針：対応する一元集合の有限商の標準根を写す。
規約：古典的な有限集合の所属判定を使用する。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の全族商から余極限への逆射。 -/
def polynomialFamilyColimitRoot (s : σ) : PolynomialFamilyColimit f := by
  classical
  exact polynomialFamilyColimitOf f {s}
    (polynomialFamilyQuotientRoot (fun t : ({s} : Finset σ) => f t)
      ⟨s, Finset.mem_singleton_self (s : σ)⟩)

/-- 概要：有限段の標準根の余極限像は一元段で選んだ同じ根と一致する。
方針：一元集合の元の有限段への包含と遷移射の根公式を使う。
規約：任意の根を含む有限段で計算できる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全族商と余極限の相互逆性。 -/
theorem polynomialFamilyColimitOf_root (T : Finset σ) (s : T) :
    polynomialFamilyColimitOf f T (polynomialFamilyQuotientRoot (fun t : T => f t) s) =
      polynomialFamilyColimitRoot f s := by
  classical
  let h : ({(s : σ)} : Finset σ) ⊆ T := Finset.singleton_subset_iff.mpr s.property
  have he := polynomialFamilyColimitOf_compatible f h
    (polynomialFamilyQuotientRoot (fun t : ({(s : σ)} : Finset σ) => f t)
      ⟨s, Finset.mem_singleton_self (s : σ)⟩)
  rw [polynomialFamilyFiniteMap_root] at he
  exact he

/-- 概要：余極限の選択根は元の多項式の根となる。
方針：一元段の根方程式を標準代数射で写し、元の係数作用を照合する。
規約：多項式は任意であり、モニック性は不要。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の全族商からの普遍射を作る。 -/
theorem polynomialFamilyColimit_eval (s : σ) :
    (f s).eval₂ (algebraMap R (PolynomialFamilyColimit f))
      (polynomialFamilyColimitRoot f s) = 0 := by
  classical
  let T : Finset σ := {s}
  let t : T := ⟨s, Finset.mem_singleton_self s⟩
  let j := polynomialFamilyColimitOf f T
  have he := congrArg j.toRingHom (polynomialFamilyQuotient_eval (fun t : T => f t) t)
  rw [Polynomial.hom_eval₂, map_zero] at he
  have hc : j.toRingHom.comp (algebraMap R (PolynomialFamilyFiniteStage f T)) =
      algebraMap R (PolynomialFamilyColimit f) := RingHom.ext j.commutes
  rw [hc] at he
  exact he

/-- 概要：有限商から全族商への標準射を余極限からの代数射に延長する。
方針：前工程の両立性と DirectLimit の普遍性を使う。
規約：係数環と根の行先を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常余極限の比較。 -/
def polynomialFamilyColimitToFull : PolynomialFamilyColimit f →ₐ[R] PolynomialFamilyQuotient f :=
  DirectLimit.Algebra.lift S d (PolynomialFamilyQuotient f)
    (polynomialFamilyFiniteToFull f)
    (fun _ _ h x => DFunLike.congr_fun (polynomialFamilyFiniteToFull_compatible f h) x)

/-- 概要：余極限から全族商への射は各有限段の標準射を延長する。
方針：DirectLimit の持ち上げの構造射上の公式。
規約：代数射の等式として述べる。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の全族商比較の相互逆性。 -/
theorem polynomialFamilyColimitToFull_comp_of (T : Finset σ) :
    (polynomialFamilyColimitToFull f).comp (polynomialFamilyColimitOf f T) =
      polynomialFamilyFiniteToFull f T := rfl

/-- 概要：全族の通常関係商から有限商余極限への代数射。
方針：余極限の根方程式を根族商の普遍射に渡す。
規約：元の係数作用を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の標準余極限比較の逆射。 -/
def polynomialFamilyFullToColimit : PolynomialFamilyQuotient f →ₐ[R] PolynomialFamilyColimit f :=
  polynomialFamilyQuotientLiftAlgHom f (polynomialFamilyColimitRoot f)
    (polynomialFamilyColimit_eval f)

/-- 概要：全族商から余極限への射は各標準根を余極限の対応する根へ送る。
方針：根族商の普遍射の根公式を使う。
規約：指定根の証明を明示する。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の全族商比較の生成元計算。 -/
theorem polynomialFamilyFullToColimit_root (s : σ) :
    polynomialFamilyFullToColimit f (polynomialFamilyQuotientRoot f s) =
      polynomialFamilyColimitRoot f s :=
  polynomialFamilyQuotientLift_root f _ _ (polynomialFamilyColimit_eval f) s

/-- 概要：全族商を経由する余極限への有限段の射は標準構造射と一致する。
方針：有限商の各標準根の像を比較する。
規約：有限段からの代数射の等式。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の余極限側の相互逆性。 -/
theorem polynomialFamilyFullToColimit_comp_toFull (T : Finset σ) :
    (polynomialFamilyFullToColimit f).comp (polynomialFamilyFiniteToFull f T) =
      polynomialFamilyColimitOf f T := by
  apply polynomialFamilyQuotientAlgHom_ext (fun t : T => f t)
  intro t
  change polynomialFamilyFullToColimit f
    (polynomialFamilyFiniteToFull f T (polynomialFamilyQuotientRoot (fun s : T => f s) t)) = _
  rw [polynomialFamilyFiniteToFull_root, polynomialFamilyFullToColimit_root,
    polynomialFamilyColimitOf_root]

/-- 概要：有限部分族の通常商の代数余極限は全族の実通常関係商と R 代数同型。
方針：普遍性で作った両方向の射を、余極限の各段と全族の標準根で比較する。
規約：モニック性・正次数・遷移射の単射性を要求しない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の通常忠実平坦性を任意族の実商へ移す。 -/
def polynomialFamilyColimitEquiv : PolynomialFamilyColimit f ≃ₐ[R] PolynomialFamilyQuotient f := by
  let F := polynomialFamilyColimitToFull f
  let G := polynomialFamilyFullToColimit f
  have hGF : G.comp F = AlgHom.id R (PolynomialFamilyColimit f) := by
    apply DirectLimit.Algebra.hom_ext
    intro T
    change (G.comp F).comp (polynomialFamilyColimitOf f T) =
      (AlgHom.id R (PolynomialFamilyColimit f)).comp (polynomialFamilyColimitOf f T)
    rw [AlgHom.comp_assoc, polynomialFamilyColimitToFull_comp_of]
    exact polynomialFamilyFullToColimit_comp_toFull f T
  have hFG : F.comp G = AlgHom.id R (PolynomialFamilyQuotient f) := by
    classical
    apply polynomialFamilyQuotientAlgHom_ext f
    intro s
    change F (G (polynomialFamilyQuotientRoot f s)) = polynomialFamilyQuotientRoot f s
    rw [polynomialFamilyFullToColimit_root]
    change polynomialFamilyColimitToFull f (polynomialFamilyColimitOf f {s}
      (polynomialFamilyQuotientRoot (fun t : ({s} : Finset σ) => f t)
        ⟨s, Finset.mem_singleton_self s⟩)) = _
    change polynomialFamilyFiniteToFull f {s}
      (polynomialFamilyQuotientRoot (fun t : ({s} : Finset σ) => f t)
        ⟨s, Finset.mem_singleton_self s⟩) = _
    exact polynomialFamilyFiniteToFull_root f {s} _
  exact
    { toFun := F
      invFun := G
      left_inv := fun x => DFunLike.congr_fun hGF x
      right_inv := fun x => DFunLike.congr_fun hFG x
      map_mul' := F.map_mul
      map_add' := F.map_add
      commutes' := F.commutes }

end SerrePositivity.BhattScholze.Andre

end MonicFamilyColimit

/-! ## 通常根族商への一変数追加

## 概要

Option で一変数を加えた多項式関係族の商を、先行族の商の上の一元 AdjoinRoot と同定する。
BS 著者版 Theorem 7.14（p.61）、BS 著者版 Remark 7.15（p.62）の通常モニック根添加の有限族への準備。

## 方針

両方の商の普遍射で相互の環射を作り、係数と標準根上で相互逆性を証明する。
代数同型として元の係数作用も保存する。

## 規約

この同型自体はモニック性や正次数を要求しない。
自由性・忠実平坦性の証明で後からモニック性と正次数を用いる。

## 使われ方

有限族の通常商の自由性と忠実平坦性を一元の結果から帰納する。
-/

@[expose] public noncomputable section MonicFamilyOptionQuotient

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：一変数追加した通常関係商は先行関係商上の一元根添加と代数同型。
方針：指定根への普遍射を両方向に作り、係数と全標準根で相互逆性を検証する。
規約：元の R 係数作用を保ち、モニック性を要求しない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の有限モニック族の通常商の自由性。 -/
def polynomialFamilyOptionEquiv {R : Type u} [CommRing R] {σ : Type v}
    (f : Option σ → Polynomial R) :
    PolynomialFamilyQuotient f ≃ₐ[R]
      AdjoinRoot ((f none).map
        (algebraMap R (PolynomialFamilyQuotient (fun s : σ => f (some s))))) := by
  let f₀ := fun s : σ => f (some s)
  let Q := PolynomialFamilyQuotient f₀
  let g := (f none).map (algebraMap R Q)
  let B := AdjoinRoot g
  let a : Option σ → B := fun s => match s with
    | none => AdjoinRoot.root g
    | some t => algebraMap Q B (polynomialFamilyQuotientRoot f₀ t)
  have ha : ∀ s, (f s).eval₂ (algebraMap R B) (a s) = 0 := by
    intro s
    cases s with
    | none =>
      have h := AdjoinRoot.eval₂_root g
      rw [Polynomial.eval₂_map] at h
      exact h
    | some t =>
      have h := congrArg (algebraMap Q B) (polynomialFamilyQuotient_eval f₀ t)
      rw [Polynomial.hom_eval₂, map_zero] at h
      exact h
  let F := polynomialFamilyQuotientLift f (algebraMap R B) a ha
  have Fcoeff (x : R) : F (algebraMap R (PolynomialFamilyQuotient f) x) =
      algebraMap R B x := polynomialFamilyQuotientLift_coeff f _ a ha x
  have Froot (s : Option σ) : F (polynomialFamilyQuotientRoot f s) = a s :=
    polynomialFamilyQuotientLift_root f _ a ha s
  let b := fun s : σ => polynomialFamilyQuotientRoot f (some s)
  have hb : ∀ s : σ, (f₀ s).eval₂ (algebraMap R (PolynomialFamilyQuotient f)) (b s) = 0 :=
    fun s => polynomialFamilyQuotient_eval f (some s)
  let j := polynomialFamilyQuotientLift f₀ (algebraMap R (PolynomialFamilyQuotient f)) b hb
  have jcoeff (x : R) : j (algebraMap R Q x) =
      algebraMap R (PolynomialFamilyQuotient f) x :=
    polynomialFamilyQuotientLift_coeff f₀ _ b hb x
  have jroot (s : σ) : j (polynomialFamilyQuotientRoot f₀ s) =
      polynomialFamilyQuotientRoot f (some s) :=
    polynomialFamilyQuotientLift_root f₀ _ b hb s
  have hj : j.comp (algebraMap R Q) = algebraMap R (PolynomialFamilyQuotient f) :=
    RingHom.ext jcoeff
  have hg : g.eval₂ j (polynomialFamilyQuotientRoot f none) = 0 := by
    rw [Polynomial.eval₂_map, hj]
    exact polynomialFamilyQuotient_eval f none
  let G := AdjoinRoot.lift j (polynomialFamilyQuotientRoot f none) hg
  have Gcoeff (x : Q) : G (algebraMap Q B x) = j x := AdjoinRoot.lift_of hg
  have Groot : G (AdjoinRoot.root g) = polynomialFamilyQuotientRoot f none :=
    AdjoinRoot.lift_root hg
  have hGF : G.comp F = RingHom.id (PolynomialFamilyQuotient f) := by
    apply polynomialFamilyQuotientHom_ext f
    · intro x
      change G (F (algebraMap R (PolynomialFamilyQuotient f) x)) = _
      rw [Fcoeff]
      change G (algebraMap Q B (algebraMap R Q x)) = _
      rw [Gcoeff, jcoeff]
      rfl
    · intro s
      change G (F (polynomialFamilyQuotientRoot f s)) = _
      rw [Froot]
      cases s with
      | none => exact Groot
      | some t =>
        change G (algebraMap Q B (polynomialFamilyQuotientRoot f₀ t)) = _
        rw [Gcoeff, jroot]
        rfl
  have hFj : F.comp j = algebraMap Q B := by
    apply polynomialFamilyQuotientHom_ext f₀
    · intro x
      change F (j (algebraMap R Q x)) = _
      rw [jcoeff, Fcoeff]
      rfl
    · intro s
      change F (j (polynomialFamilyQuotientRoot f₀ s)) = _
      rw [jroot, Froot]
  have hFG : F.comp G = RingHom.id B := by
    apply AdjoinRoot.ringHom_ext
    · change (F.comp G).comp (AdjoinRoot.of g) = AdjoinRoot.of g
      rw [RingHom.comp_assoc, AdjoinRoot.lift_comp_of]
      exact hFj
    · change F (G (AdjoinRoot.root g)) = AdjoinRoot.root g
      rw [Groot, Froot]
  exact
    { toFun := F
      invFun := G
      left_inv := fun x => RingHom.congr_fun hGF x
      right_inv := fun x => RingHom.congr_fun hFG x
      map_mul' := F.map_mul
      map_add' := F.map_add
      commutes' := Fcoeff }

end SerrePositivity.BhattScholze.Andre

end MonicFamilyOptionQuotient

/-! ## 通常根族商の再添字付け

## 概要

添字集合の同値で多項式族を移しても通常の根族商は元の係数環上で代数同型となる。
BS 著者版 Theorem 7.14（p.61）、BS 著者版 Remark 7.15（p.62）の有限族から任意族への準備。

## 方針

両方向の指定根への普遍射を作り、係数と根に関する外延性で相互逆性を示す。

## 規約

モニック性や正次数を使わない。宇宙の異なる添字集合の同値も許す。

## 使われ方

有限集合に対する空集合・Option 帰納で根族商の自由性を移す。
-/

@[expose] public noncomputable section MonicFamilyQuotientReindex

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：同値で再添字付けした多項式族の通常商は元の係数環上で代数同型。
方針：普遍射を両方向に作り、生成元の値から相互逆性を確認する。
規約：多項式族は任意。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限族の帰納と遷移射の比較。 -/
def polynomialFamilyReindexEquiv {R : Type u} [CommRing R] {σ : Type v} {τ : Type w}
    (e : σ ≃ τ) (f : σ → Polynomial R) :
    PolynomialFamilyQuotient f ≃ₐ[R] PolynomialFamilyQuotient (fun t : τ => f (e.symm t)) := by
  let g := fun t : τ => f (e.symm t)
  let Q := PolynomialFamilyQuotient f
  let T := PolynomialFamilyQuotient g
  let a := fun s : σ => polynomialFamilyQuotientRoot g (e s)
  have ha : ∀ s, (f s).eval₂ (algebraMap R T) (a s) = 0 := by
    intro s
    simpa only [g, Equiv.symm_apply_apply] using polynomialFamilyQuotient_eval g (e s)
  let b := fun t : τ => polynomialFamilyQuotientRoot f (e.symm t)
  have hb : ∀ t, (g t).eval₂ (algebraMap R Q) (b t) = 0 :=
    fun t => polynomialFamilyQuotient_eval f (e.symm t)
  let F := polynomialFamilyQuotientLift f (algebraMap R T) a ha
  let G := polynomialFamilyQuotientLift g (algebraMap R Q) b hb
  have Fcoeff (x : R) : F (algebraMap R Q x) = algebraMap R T x :=
    polynomialFamilyQuotientLift_coeff f _ a ha x
  have Gcoeff (x : R) : G (algebraMap R T x) = algebraMap R Q x :=
    polynomialFamilyQuotientLift_coeff g _ b hb x
  have Froot (s : σ) : F (polynomialFamilyQuotientRoot f s) =
      polynomialFamilyQuotientRoot g (e s) := polynomialFamilyQuotientLift_root f _ a ha s
  have Groot (t : τ) : G (polynomialFamilyQuotientRoot g t) =
      polynomialFamilyQuotientRoot f (e.symm t) := polynomialFamilyQuotientLift_root g _ b hb t
  have hGF : G.comp F = RingHom.id Q := by
    apply polynomialFamilyQuotientHom_ext f
    · intro x
      change G (F (algebraMap R Q x)) = algebraMap R Q x
      rw [Fcoeff, Gcoeff]
    · intro s
      change G (F (polynomialFamilyQuotientRoot f s)) = polynomialFamilyQuotientRoot f s
      rw [Froot, Groot, Equiv.symm_apply_apply]
  have hFG : F.comp G = RingHom.id T := by
    apply polynomialFamilyQuotientHom_ext g
    · intro x
      change F (G (algebraMap R T x)) = algebraMap R T x
      rw [Gcoeff, Fcoeff]
    · intro t
      change F (G (polynomialFamilyQuotientRoot g t)) = polynomialFamilyQuotientRoot g t
      rw [Groot, Froot, Equiv.apply_symm_apply]
  exact
    { toFun := F
      invFun := G
      left_inv := fun x => RingHom.congr_fun hGF x
      right_inv := fun x => RingHom.congr_fun hFG x
      map_mul' := F.map_mul
      map_add' := F.map_add
      commutes' := polynomialFamilyQuotientLift_coeff f _ a ha }

end SerrePositivity.BhattScholze.Andre

end MonicFamilyQuotientReindex

/-! ## 有限モニック族の通常商の自由性と忠実平坦性

## 概要

有限な正次数モニック多項式族に独立な根を添加した通常商は、係数環上自由かつ忠実平坦。
BS 著者版 Theorem 7.14（p.61）、BS 著者版 Remark 7.15（p.62）の有限族の通常代数部分である。

## 方針

有限添字集合を空集合・Option・再添字付けで帰納する。
一変数追加の代数同型により AdjoinRoot のモニック剰余基底を重ね、
非零係数環では正次数から各段の非零性を証明する。

## 規約

零係数環を許す。通常の商の結果であり、完備化や perfectoid 化後の忠実平坦性は含まない。
原典の BS 著者版 Proposition 7.11 の経路と異なる、明示的な通常根添加の計算である。

## 使われ方

任意族の通常商を有限部分族から組み立てる際の自由性・忠実平坦性の入力に用いる。
-/

@[expose] public noncomputable section MonicFiniteFamilyFlat

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：非零係数環上の有限な正次数モニック族の通常商は自由かつ非零。
方針：有限型の空集合・Option 帰納で自由基底と非零性を同時に保持する。
規約：各多項式に正次数を要求し、定数 1 による零商を除外する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限族の通常商の忠実平坦性。 -/
theorem monicFiniteFamilyQuotient_free_nontrivial
    {R : Type u} [CommRing R] [Nontrivial R] {σ : Type v} [Finite σ]
    (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    Module.Free R (PolynomialFamilyQuotient f) ∧ Nontrivial (PolynomialFamilyQuotient f) := by
  let P : Type v → Prop := fun τ => ∀ (g : τ → Polynomial R),
    (∀ t, (g t).Monic) → (∀ t, 0 < (g t).natDegree) →
    Module.Free R (PolynomialFamilyQuotient g) ∧ Nontrivial (PolynomialFamilyQuotient g)
  have hall : P σ := Finite.induction_empty_option (P := P)
    (fun {α β} e ih => by
      intro g hg hd
      obtain ⟨hfree, hne⟩ := ih (fun s : α => g (e s)) (fun s => hg (e s)) (fun s => hd (e s))
      let := hfree
      let := hne
      let e' : PolynomialFamilyQuotient g ≃ₐ[R]
          PolynomialFamilyQuotient (fun s : α => g (e s)) := by
        simpa only [Equiv.symm_symm] using polynomialFamilyReindexEquiv e.symm g
      exact ⟨Module.Free.of_equiv e'.symm.toLinearEquiv, e'.toEquiv.nontrivial⟩)
    (by
      intro g _ _
      have hI : polynomialFamilyRelationIdeal g = ⊥ := by
        simp only [polynomialFamilyRelationIdeal, Set.range_eq_empty, Ideal.span_empty]
      change Module.Free R (MvPolynomial PEmpty R ⧸ polynomialFamilyRelationIdeal g) ∧
        Nontrivial (MvPolynomial PEmpty R ⧸ polynomialFamilyRelationIdeal g)
      rw [hI]
      let e := AlgEquiv.quotientBot R (MvPolynomial PEmpty R)
      exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv, e.toEquiv.nontrivial⟩)
    (by
      intro α _ ih g hg hd
      let g₀ := fun s : α => g (some s)
      let Q := PolynomialFamilyQuotient g₀
      obtain ⟨hfree, hne⟩ := ih g₀ (fun s => hg (some s)) (fun s => hd (some s))
      let := hfree
      let := hne
      let h := (g none).map (algebraMap R Q)
      let B := AdjoinRoot h
      have hm : h.Monic := (hg none).map (algebraMap R Q)
      have hn : 0 < h.natDegree := by
        rw [(hg none).natDegree_map]
        exact hd none
      let : Nontrivial B := (AdjoinRoot.of.injective_of_monic_of_degree_pos hm
        (Polynomial.natDegree_pos_iff_degree_pos.mp hn)).nontrivial
      let : Module.Free Q B := hm.free_adjoinRoot
      let : Module.Free R B := Module.Free.trans (R := R) (S := Q) (M := B)
      let e := polynomialFamilyOptionEquiv g
      exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv, e.toEquiv.nontrivial⟩) σ
  exact hall f hf hdeg

/-- 概要：任意可換環上の有限正次数モニック族の通常商は自由かつ忠実平坦。
方針：非零係数環では前定理の自由性と非零性を使い、零係数環は加群の自明性で処理する。
規約：標準商の元の係数作用を保つ。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の通常の有限同時根添加。 -/
theorem monicFiniteFamilyQuotient_free_faithfullyFlat
    {R : Type u} [CommRing R] {σ : Type v} [Finite σ]
    (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    Module.Free R (PolynomialFamilyQuotient f) ∧
      Module.FaithfullyFlat R (PolynomialFamilyQuotient f) := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · let := hs
    let : Subsingleton (PolynomialFamilyQuotient f) := Module.subsingleton R _
    refine ⟨inferInstance, ?_⟩
    rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
    refine ⟨inferInstance, ?_⟩
    intro N _ _ _
    exact Module.subsingleton R N
  · let := hn
    obtain ⟨hfree, hne⟩ := monicFiniteFamilyQuotient_free_nontrivial f hf hdeg
    let := hfree
    let := hne
    exact ⟨inferInstance, inferInstance⟩

/-- 概要：有限正次数モニック族の根を同時に持つ自由忠実平坦な通常拡大が存在する。
方針：標準の根族商とその係数射・変数像を取る。
規約：R と添字を同じ宇宙に置き、拡大も同じ宇宙に取る。perfectoid 性は結論しない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の通常同時根添加の有限段。 -/
theorem exists_finiteMonicRootedFaithfullyFlat
    {R : Type u} [CommRing R] {σ : Type u} [Finite σ]
    (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      (letI := φ.toAlgebra; Module.Free R T ∧ Module.FaithfullyFlat R T) ∧
        ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  refine ⟨PolynomialFamilyQuotient f, inferInstance, algebraMap R _,
    polynomialFamilyQuotientRoot f, ?_, polynomialFamilyQuotient_eval f⟩
  rw [toAlgebra_algebraMap]
  exact monicFiniteFamilyQuotient_free_faithfullyFlat f hf hdeg

end SerrePositivity.BhattScholze.Andre

end MonicFiniteFamilyFlat

/-! ## 任意モニック族の通常根商の忠実平坦性

## 概要

任意個の正次数モニック多項式に独立な根を添加した通常の関係商は、元の係数環上忠実平坦。
BS 著者版 Theorem 7.14（p.61）、BS 著者版 Remark 7.15（p.62）の通常代数部分を扱う。

## 方針

有限部分族の自由忠実平坦性と、固定基底上の忠実平坦代数の有向余極限の既存定理を使う。
全族の実関係商との R 代数同型を通じて元の係数作用の忠実平坦性を得る。

## 規約

零係数環と任意濃度の族を許す。自由加群の余極限の自由性は推論しない。
完備化・perfectoid 化後の忠実平坦性はこの通常代数の結果には含めない。
原典の BS 著者版 Proposition 7.11 の経路と異なる、明示的商と有限部分族の余極限による計算である。

## 使われ方

pd 計算の係数商に現れる任意モニック族の通常商の忠実平坦性を供給する。
-/

@[expose] public noncomputable section MonicFamilyFaithfullyFlat

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {R σ : Type u} [CommRing R]

/-- 概要：正次数モニック族の有限商余極限は元の係数環上忠実平坦。
方針：各有限商の忠実平坦性と、R 代数の有向余極限の忠実平坦性を適用する。
規約：遷移射の単射性は不要であり、全族の有限性は要求しない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の任意同時根添加の通常忠実平坦性。 -/
theorem monicFamilyColimit_faithfullyFlat (f : σ → Polynomial R)
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    Module.FaithfullyFlat R (PolynomialFamilyColimit f) := by
  apply Transfinite.faithfullyFlat_algebraDirectLimit
    (fun T : Finset σ => PolynomialFamilyFiniteStage f T)
    (fun _ _ h => polynomialFamilyFiniteMap f h)
  intro T
  exact (monicFiniteFamilyQuotient_free_faithfullyFlat (fun t : T => f t)
    (fun t => hf t) (fun t => hdeg t)).2

/-- 概要：任意正次数モニック族の全関係を課した実通常商は元の係数環上忠実平坦。
方針：有限商余極限との R 代数同型で忠実平坦性を移す。
規約：元の標準係数射に関して述べ、零係数環を排除しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常モニック係数商の忠実平坦性入力。 -/
theorem polynomialFamilyQuotient_faithfullyFlat (f : σ → Polynomial R)
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    Module.FaithfullyFlat R (PolynomialFamilyQuotient f) := by
  let := monicFamilyColimit_faithfullyFlat f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv R (PolynomialFamilyColimit f)
    (polynomialFamilyColimitEquiv f).symm.toLinearEquiv

/-- 概要：任意正次数モニック族の根を同時に持つ通常忠実平坦拡大が同じ宇宙に存在する。
方針：全族の標準関係商と標準根を取る。
規約：perfectoid 性・完備性・p 完全忠実平坦性は結論しない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の通常同時根添加部分の公開結果。 -/
theorem exists_familyMonicRootedFaithfullyFlat (f : σ → Polynomial R)
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      (letI := φ.toAlgebra; Module.FaithfullyFlat R T) ∧
        ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  refine ⟨PolynomialFamilyQuotient f, inferInstance, algebraMap R _,
    polynomialFamilyQuotientRoot f, ?_, polynomialFamilyQuotient_eval f⟩
  rw [toAlgebra_algebraMap]
  exact polynomialFamilyQuotient_faithfullyFlat f hf hdeg

end SerrePositivity.BhattScholze.Andre

end MonicFamilyFaithfullyFlat

/-! ## 全族の通常関係商と係数商の交換

## 概要

任意多項式族の通常商を係数イデアルでさらに割る操作を、係数変更した多項式族の通常商と同定する。
BS 著者版 Corollary 2.39（p.25）、BS 著者版 Remark 7.15（p.62）の raw 除算包の実剰余計算に使う。

## 方針

多変数多項式環と係数商の交換同型を関係イデアルの商まで降下する。
代表元の係数写像を明示して、元の係数環商の作用を固定する。

## 規約

モニック性・正次数・族の有限性はこの同型には不要。
通常商の計算であり、導来基底変更との比較は別工程である。

## 使われ方

raw φ/p 包の初期係数商を、mod p のモニック関係の冪商として表示する。
-/

@[expose] public noncomputable section MonicFamilyCoefficientQuotient

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {R : Type u} [CommRing R] {σ : Type v}
variable (I : Ideal R) (f : σ → Polynomial R)
local notation "IB" => I.map (MvPolynomial.C : R →+* MvPolynomial σ R)
local notation "J" => polynomialFamilyRelationIdeal f
local notation "Jbar" => polynomialFamilyRelationIdeal
  (fun s => Polynomial.map (Ideal.Quotient.mk I) (f s))

/-- 概要：係数商で全族の関係イデアルは係数変更した関係イデアルへ写る。
方針：係数商の可換公式と多項式評価の自然性を生成元に適用する。
規約：元の全族の添字を保持する。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の実係数商の同定。 -/
theorem polynomialFamilyIdeal_map_coefficientQuotient :
    ((J).map (Ideal.Quotient.mk IB)).map
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingHom = Jbar := by
  rw [Ideal.map_map, monicPowerFamilyCoefficientQuotient_comp]
  simp only [polynomialFamilyRelationIdeal, Ideal.map_span, ← Set.range_comp']
  congr 1
  congr 1
  funext s
  exact monicRelation_map _ _ _

/-- 概要：係数イデアルと全族の関係を同時に課す商は、係数変更後の全族商と同型。
方針：二重商と多変数係数商の交換同型を合成する。
規約：モニック性を必要としない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常剰余環を固定する。 -/
def polynomialFamilyBaseQuotientEquiv :
    (MvPolynomial σ R ⧸ (IB ⊔ J)) ≃+*
      PolynomialFamilyQuotient (fun s => (f s).map (Ideal.Quotient.mk I)) :=
  (DoubleQuot.quotQuotEquivQuotSup IB J).symm.trans
    (Ideal.quotientEquiv _ _
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingEquiv
      (polynomialFamilyIdeal_map_coefficientQuotient I f).symm)

/-- 概要：係数商の同型は任意代表元の係数を商へ写す。
方針：二重商と係数商の代表元公式を使う。
規約：全族の変数は変えない。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の元の係数射の追跡。 -/
theorem polynomialFamilyBaseQuotientEquiv_mk (x : MvPolynomial σ R) :
    polynomialFamilyBaseQuotientEquiv I f (Ideal.Quotient.mk (IB ⊔ J) x) =
      Ideal.Quotient.mk Jbar (MvPolynomial.map (Ideal.Quotient.mk I) x) := by
  change Ideal.Quotient.mk Jbar
    ((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm
      (Ideal.Quotient.mk IB x)) = _
  congr 1
  exact DFunLike.congr_fun (monicPowerFamilyCoefficientQuotient_comp σ R I) x

end SerrePositivity.BhattScholze.Andre

end MonicFamilyCoefficientQuotient
