-- 将来の置き場所：SerrePositivity.EInfinity.PowerOperation.*（新設、BarrattEccles・Operad の隣。調整役の決定、main 431c40741、M14。担当は A4 の中身を書く段階で決める）
-- 設計書：formalization-plans/bhatt-scholze/a4-design.md G-A4-1。基準コミット 972bb7f53。ビルドしない。
module

public import Mathlib.FieldTheory.Finite.Basic
public import SerrePositivity.EInfinity.Perfectoidization.Comparison
public import SerrePositivity.InfinityCategories.Derived.Homology
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluation
-- 取り込み時の依存先：drafts/DerivedGeneral/ScalarRestriction.lean。
-- 本ファイルは drafts/Shared/CosimplicialEInfinity.lean（余単体的可換環の Tot_{E∞}）を使う。

/-!
# E∞-F_p 代数の冪作用 P⁰（[Lur11, §2.2]、Berger–Fresse、May）

## 概要
標数 p の E∞ 代数（E∞-F_p 代数、ここでは F_p 代数 k 上の Barratt–Eccles 代数）のホモトピー π_* に作用する冪作用のうち P⁰ を定義し、
(i) π_0 では Frobenius x ↦ x^p、(ii) π_n（n > 0、ホモロジー的）では零（[Lur11, Rem 2.2.7]）、(iii) 余単体的（および単体的余単体的）可換 F_p 代数の
levelwise Frobenius x ↦ x^p が Tot_{E∞}（実現）の P⁰ を誘導すること、を述べる。

## 方針
Barratt–Eccles 作用素 E(p) の F_p 上の作用から、x ∈ π_n に対し P⁰(x) を p 乗の作用素の標準元（Steenrod の構成、Berger–Fresse §2、May の
P^i の i = 0 の成分）で定義する。(ii) は Lurie の議論（DAG XIII、または Mandell）。(iii) は余鎖の Frobenius と作用素の p 乗の一致。

## 規約
cohomological な添字では「π_n（n > 0）」は「H^{−n}（n > 0）」。coconnective な対象（余単体的 Tot）には正次数のホモトピーがなく、
正次数は単体的方向（Kan 延長の分解）から来る。EInfinity の operad の具体的な型に合わせる（要確認）。

## 使われ方
Lemma 8.4（A4）：Δ_perf/p で P⁰ が可逆 ⇒ coconnective。Example 8.3。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.EInfinity

open CategoryTheory SSet SerrePositivity.InfinityCategories BarrattEccles Perfectoidization
open SerrePositivity.BhattScholze.PerfectoidizationInterface (A_R)
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- 概要：E∞-k 代数（k は F_p 代数）のホモトピー π_n（整数次数）。
方針：`CAlg_R k` の頂点の忘却像の H^{−n}。
規約：ホモロジー的添字。
使われ方：P⁰ の定義域。 -/
def homotopy (k : Type u) [CommRing k] (p : ℕ) (X : (CAlg_R k) _⦋0⦌) : ℤ → Type u
  | 0 => cAlgH0Ring X
  | .ofNat (n+1) => derivedInfinityHomology k (-((n+1 : ℕ) : ℤ)) ((cAlgForgetDerived k).app _ X)
  | .negSucc n => derivedInfinityHomology k (-(Int.negSucc n)) ((cAlgForgetDerived k).app _ X)

instance homotopyZeroRing (X : (CAlg_R k) _⦋0⦌) : CommRing (homotopy k p X 0) :=
  inferInstanceAs (CommRing (cAlgH0Ring X))

instance homotopyAddGroup (X : (CAlg_R k) _⦋0⦌) (n : ℤ) : AddCommGroup (homotopy k p X n) := by
  match n with
  | 0 => exact inferInstanceAs (AddCommGroup (cAlgH0Ring X))
  | .ofNat (i+1) => unfold homotopy; infer_instance
  | .negSucc i => unfold homotopy; infer_instance

def homotopyZeroRingEquiv (X : (CAlg_R k) _⦋0⦌) : homotopy k p X 0 ≃+* cAlgH0Ring X :=
  RingEquiv.refl _

def homotopyCohomology (X : (CAlg_R k) _⦋0⦌) (n : ℤ) :
    homotopy k p X n ≃+ derivedInfinityHomology k (-n) ((cAlgForgetDerived k).app _ X) := by
  sorry -- n=0 は同じ cofibrant 代表の忘却と H⁰ の比較。他の次数は定義どおり

def homotopyMap {X Y : (CAlg_R k) _⦋0⦌} (f : SSet.Edge X Y) (n : ℤ) :
    homotopy k p X n →+ homotopy k p Y n :=
  (homotopyCohomology k p Y n).symm.toAddMonoidHom.comp
    ((derivedInfinityHomologyMap k (-n) (f.map (cAlgForgetDerived k)).toTruncated).hom.toAddMonoidHom.comp
      (homotopyCohomology k p X n).toAddMonoidHom)

/-- 概要：冪作用 P⁰ : π_n(X) → π_n(X)（加法的、π_* 全体で定義）。
方針：Barratt–Eccles 作用素の p 乗の作用の標準元で定義（Steenrod／May の P^0）。
規約：k 線形ではない（φ_k 半線形）。
使われ方：Lemma 8.4。
要確認：EInfinity の operad の作用の型（`Operad`、`BarrattEccles` の E(p) と k[Σ_p] 加群の構造）。 -/
def powerOperationZero (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (X : (CAlg_R k) _⦋0⦌) (n : ℤ) : homotopy k p X n →+ homotopy k p X n := by
  sorry -- M14：Barratt–Eccles の標準の p 項演算がホモトピーに誘導する加法写像

/-- 概要：(i) π_0 では P⁰ は Frobenius x ↦ x^p。
方針：作用素の次数 0 成分は積。
規約：π_0 は可換環。
使われ方：H⁰(Δ_perf) の Frobenius の同定（Lemma 8.4 (b)）。 -/
theorem powerOperationZero_zero (X : (CAlg_R k) _⦋0⦌) (x : homotopy k p X 0) :
    homotopyZeroRingEquiv k p X (powerOperationZero k p X 0 x) =
      (homotopyZeroRingEquiv k p X x)^p := by
  sorry -- M14：次数零の作用は H⁰ の p 重積

/-- 概要：(ii) [Lur11, Rem 2.2.7]：n > 0 なら P⁰ = 0 on π_n。
方針：Lurie DAG XIII §2.2（E∞-F_p 代数の冪作用の性質）、または Mandell の E∞-F_p 代数の P⁰ の議論。
規約：ホモロジー的 n > 0。
使われ方：Lemma 8.4 (a)。 -/
theorem powerOperationZero_pos (X : (CAlg_R k) _⦋0⦌) (n : ℤ) (hn : 0 < n) :
    powerOperationZero k p X n = 0 := by sorry

/-- 概要：P⁰ は E∞ 代数の射で自然。
方針：作用素の作用の自然性。
規約：—
使われ方：Frobenius の自己同型が P⁰ と可換（Δ_perf/p）。 -/
theorem powerOperationZero_natural {X Y : (CAlg_R k) _⦋0⦌} (f : SSet.Edge X Y) (n : ℤ)
    (x : homotopy k p X n) :
    homotopyMap k p f n (powerOperationZero k p X n x) = powerOperationZero k p Y n (homotopyMap k p f n x) := by
  sorry -- E∞ 代数の射は Barratt–Eccles の演算を保つ

/-- 概要：P⁰ を忘却 U : CAlg_k → D(k)上の **Frobenius 半線形な coherent 自然変換**として（Lurie DAG XIII Constr 2.2.6 の強さ。W9-II-02）。
方針：Barratt–Eccles で実装するなら、この強さと Lurie 型演算との対応を仕様に含める。π_n 上の作用 `powerOperationZero` はその成分。
規約：E∞ 代数の射で自然、極限・幾何学的実現の錐と両立。
使われ方：(iii)。 -/
def powerOperationZero_natTrans : FunctorHom (cAlgForgetDerived k)
    (cAlgForgetDerived k ≫ derivedInfinityRestrictScalars (frobenius k p)) := by
  sorry -- D5-03：p 乗作用は k 線形になるよう終域のスカラーを φ_k に沿って制限する

def powerOperationZero_primeField (p : ℕ) [Fact p.Prime] :
    FunctorHom (cAlgForgetDerived (ZMod p)) (cAlgForgetDerived (ZMod p)) := by
  let U := cAlgForgetDerived (ZMod p)
  have α : FunctorHom U (U ≫ derivedInfinityRestrictScalars (RingHom.id (ZMod p))) := by
    simpa only [ZMod.frobenius_zmod] using powerOperationZero_natTrans (ZMod p) p
  exact α ≫ ((derivedInfinityRestrictScalars_id (S := ZMod p)).precomp U).hom ≫
    eqToHom (by simp)

/-- 係数の読み替えは Hⁱ の台の加法群を変えない。 -/
def restrictHomologyAddEquiv (M : (derivedInfinityCategory k) _⦋0⦌) (i : ℤ) :
    derivedInfinityHomology k i ((derivedInfinityRestrictScalars (frobenius k p)).app _ M) ≃+
      derivedInfinityHomology k i M := by
  sorry -- M13：係数制限した複体の cycles と boundaries は元の加法群のもの

theorem powerOperationZero_component (X : (CAlg_R k) _⦋0⦌) (n : ℤ) (x : homotopy k p X n) :
    let U := cAlgForgetDerived k
    let e := Classical.choose (homotopyCategory_homMk_surjective _ _
      (functorHomEvaluate (powerOperationZero_natTrans k p) X))
    homotopyCohomology k p X n (powerOperationZero k p X n x) =
      restrictHomologyAddEquiv k p (U.app _ X) (-n)
        ((derivedInfinityHomologyMap k (-n) e) (homotopyCohomology k p X n x)) := by
  sorry -- M14：半線形な coherent 変換の成分が各 π_n の P⁰ を誘導する

abbrev frobeniusRestriction := Under.map (CommRingCat.ofHom (frobenius k p))

/-- B の元を p 乗する、φ_k に沿う k 代数の射。零環も含める。 -/
def discreteFrobenius (B : A_R k) : B ⟶ (frobeniusRestriction k p).obj B :=
  Under.homMk (CommRingCat.ofHom ({
    toFun := fun x => x^p
    map_one' := one_pow _
    map_mul' := fun x y => mul_pow x y p
    map_zero' := zero_pow (Fact.out : Nat.Prime p).ne_zero
    map_add' := by sorry -- p は構造射によって B でも零。二項展開
    } : B.right →+* B.right)) (by sorry) -- 構造射は p 乗と可換

def cosimplicialFrobenius (X : Cosimplicial.CosimplicialAlgebra k) :
    X ⟶ X ⋙ frobeniusRestriction k p where
  app n := discreteFrobenius k p (X.obj n)
  naturality := by sorry -- 各射は環準同型

/-- 制限は右随伴なので Tot の指定された極限錐を保つ。 -/
def totRestrictFrobeniusIso (X : Cosimplicial.CosimplicialAlgebra k) :
    VertexIso (Cosimplicial.totEInfinity k (X ⋙ frobeniusRestriction k p))
      ((cAlgRestrictScalars (frobenius k p)).app _ (Cosimplicial.totEInfinity k X)) := by
  sorry -- 各項の cAlgRestrictScalars_algebraEmbedding から totEInfinity_isLimitCone を比較

/-- 概要：(iii) 離散な可換 k 代数 B では P⁰_{HB} = H(Frob_B)。U が極限と幾何学的実現を保ち P⁰ が coherent な自然変換なので、この同定は
余単体的 Tot_{E∞}(X^•) と単体的実現へ移る：levelwise Frobenius x ↦ x^p が Tot・実現の P⁰ を誘導する。
方針：自然変換の錐との両立（W9-II-02 で訂正：**通常の p 重 cup 積による説明は誤り**。P⁰ は次数を保つが p 重 cup 積は次数 q を pq にする。
S¹ の mod 2 で x ∪ x = 0 だが Frobenius は恒等）。
規約：Shared/CosimplicialEInfinity の `totEInfinity`。
使われ方：Lemma 8.4 (a)：Δ_perf/p の塔の shift が P⁰ と同じ作用を誘導する（G-A3-9 の模型の φ との比較と合わせて）。 -/
theorem powerOperationZero_eq_frobenius_discrete (B : A_R k) :
    let X := (algebraEmbedding k).app _ (nerveVertex B)
    let U := cAlgForgetDerived k
    let f := (nerve.edgeMk (discreteFrobenius k p B)).map (algebraEmbedding k ≫ U)
    functorHomEvaluate (powerOperationZero_natTrans k p) X =
      Truncated.HomotopyCategory.homMk f.toTruncated ≫
        ((cAlgRestrictScalars_algebraEmbedding (frobenius k p) B).map U).hom ≫
        ((cAlgRestrictScalars_forget (frobenius k p)).app X).hom := by
  sorry -- 離散 B で P⁰ は Frobenius。φ_k に沿って B の構造射を読み替えた標的へ送る

theorem powerOperationZero_eq_frobenius_tot (X : Cosimplicial.CosimplicialAlgebra k) :
    let T := Cosimplicial.totEInfinity k X
    let U := cAlgForgetDerived k
    let f := (Cosimplicial.totEInfinity_map k (cosimplicialFrobenius k p X)).map U
    functorHomEvaluate (powerOperationZero_natTrans k p) T =
      Truncated.HomotopyCategory.homMk f.toTruncated ≫ ((totRestrictFrobeniusIso k p X).map U).hom ≫
        ((cAlgRestrictScalars_forget (frobenius k p)).app T).hom := by
  sorry -- 離散成分との coherent な比較を全余面・余退化とともに極限錐に移す

end SerrePositivity.EInfinity
