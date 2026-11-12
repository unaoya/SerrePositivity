-- 将来の置き場所：SerrePositivity.EInfinity.PowerOperation.*（新設、BarrattEccles・Operad の隣。調整役の決定、main 431c40741、M14。担当は A4 の中身を書く段階で決める）
-- 設計書：formalization-plans/bhatt-scholze/a4-design.md G-A4-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import Mathlib.FieldTheory.Finite.Basic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Homology
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation
-- 取り込み時の依存先：drafts/DerivedGeneral/ScalarRestriction.lean。
-- 本ファイルは drafts/Shared/CosimplicialEInfinity.lean（余単体的可換環の Tot_{E∞}）を使う。

/-!
# E∞-F_p 代数の冪作用 P⁰（[Lur11, §2.2]、Berger–Fresse、May）

## 概要
標数 p の E∞ 代数のホモトピー π_* に作用する冪作用のうち P⁰ を定義し、
(i) π_0 では Frobenius x ↦ x^p、(ii) π_n（n > 0、ホモロジー的）では零（[Lur11, Rem 2.2.7]）、(iii) 余単体的（および単体的余単体的）可換 F_p 代数の
levelwise Frobenius x ↦ x^p が Tot_{E∞}（実現）の P⁰ を誘導すること、を述べる。

## 方針
DAG XIII Construction 2.2.6 に対応する半線形自然変換を界面から読む。
零次の環、係数制限、離散入力と Tot での値には、同じ界面の比較を用いる。

## 規約
cohomological な添字では「π_n（n > 0）」は「H^{−n}（n > 0）」。coconnective な対象（余単体的 Tot）には正次数のホモトピーがなく、
正次数は単体的方向（Kan 延長の分解）から来る。

## 使われ方
Lemma 8.4（A4）：Δ_perf/p で P⁰ が可逆 ⇒ coconnective。Example 8.3。
-/

@[expose] public section
noncomputable section
universe u

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.EInfinity

open CategoryTheory SSet SerrePositivity.InfinityCategories Perfectoidization
open SerrePositivity.BhattScholze.PerfectoidizationInterface (A_R)
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- 概要：E∞-k 代数（k は F_p 代数）のホモトピー π_n（整数次数）。
方針：`CAlg_R k` の頂点の忘却像の H^{−n}。
規約：ホモロジー的添字。
使われ方：P⁰ の定義域。 -/
def homotopy (k : Type u) [CommRing k] (p : ℕ) (X : (E.CAlg k) _⦋0⦌) : ℤ → Type u
  | 0 => cAlgH0Ring (E := E) X
  | .ofNat (n+1) => derivedInfinityHomology k (-((n+1 : ℕ) : ℤ)) ((E.forget k).app _ X)
  | .negSucc n => derivedInfinityHomology k (-(Int.negSucc n)) ((E.forget k).app _ X)

instance homotopyZeroRing (X : (E.CAlg k) _⦋0⦌) : CommRing (homotopy (E := E) k p X 0) :=
  inferInstanceAs (CommRing (cAlgH0Ring (E := E) X))

instance homotopyAddGroup (X : (E.CAlg k) _⦋0⦌) (n : ℤ) : AddCommGroup (homotopy (E := E) k p X n) := by
  match n with
  | 0 => exact inferInstanceAs (AddCommGroup (cAlgH0Ring (E := E) X))
  | .ofNat (i+1) => unfold homotopy; infer_instance
  | .negSucc i => unfold homotopy; infer_instance

def homotopyZeroRingEquiv (X : (E.CAlg k) _⦋0⦌) : homotopy (E := E) k p X 0 ≃+* cAlgH0Ring (E := E) X :=
  RingEquiv.refl _

def homotopyCohomology (X : (E.CAlg k) _⦋0⦌) (n : ℤ) :
    homotopy (E := E) k p X n ≃+ derivedInfinityHomology k (-n) ((E.forget k).app _ X) := by
  match n with
  | 0 =>
    exact ((E.pi0_forget k).app (SSet.HomotopyCategory.mk X)).toLinearEquiv.toAddEquiv
  | .ofNat (n + 1) => exact AddEquiv.refl _
  | .negSucc n => exact AddEquiv.refl _

def homotopyMap {X Y : (E.CAlg k) _⦋0⦌} (f : SSet.Edge X Y) (n : ℤ) :
    homotopy (E := E) k p X n →+ homotopy (E := E) k p Y n :=
  (homotopyCohomology (E := E) k p Y n).symm.toAddMonoidHom.comp
    ((derivedInfinityHomologyMap k (-n) (f.map (E.forget k)).toTruncated).hom.toAddMonoidHom.comp
      (homotopyCohomology (E := E) k p X n).toAddMonoidHom)

/-- 概要：冪作用 P⁰ : π_n(X) → π_n(X)（加法的、π_* 全体で定義）。
方針：DAG XIII Construction 2.2.6 の半線形変換をホモロジーに送り、係数制限の自然比較で台を読む。
規約：k 線形ではない（φ_k 半線形）。
使われ方：Lemma 8.4。
 -/
def powerOperationZero (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (X : (E.CAlg k) _⦋0⦌) (n : ℤ) : homotopy (E := E) k p X n →+ homotopy (E := E) k p X n := by
  let h := (cohomologyOnHo k (-n)).map (functorHomEvaluate (E.powerOp0 k p) X)
  exact (homotopyCohomology (E := E) k p X n).symm.toAddMonoidHom.comp
    ((E.restrictD_homology (frobenius k p) (-n) (atVertex (E.forget k) X)).toAddMonoidHom.comp
      (h.hom.toAddMonoidHom.comp (homotopyCohomology (E := E) k p X n).toAddMonoidHom))

/-- 概要：(i) π_0 では P⁰ は Frobenius x ↦ x^p。
方針：作用素の次数 0 成分は積。
規約：π_0 は可換環。
使われ方：H⁰(Δ_perf) の Frobenius の同定（Lemma 8.4 (b)）。 -/
theorem powerOperationZero_zero (X : (E.CAlg k) _⦋0⦌) (x : homotopy (E := E) k p X 0) :
    homotopyZeroRingEquiv (E := E) k p X (powerOperationZero (E := E) k p X 0 x) =
      (homotopyZeroRingEquiv (E := E) k p X x)^p := by
  sorry -- E.powerOp0_zero と E.pi0_forget の成分で共役する

/-- 概要：(ii) [Lur11, Rem 2.2.7]：n > 0 なら P⁰ = 0 on π_n。
方針：Lurie DAG XIII §2.2（E∞-F_p 代数の冪作用の性質）、または Mandell の E∞-F_p 代数の P⁰ の議論。
規約：ホモロジー的 n > 0。
使われ方：Lemma 8.4 (a)。 -/
theorem powerOperationZero_pos (X : (E.CAlg k) _⦋0⦌) (n : ℤ) (hn : 0 < n) :
    powerOperationZero (E := E) k p X n = 0 := by
  sorry -- E.powerOp0_pos を加法同型で移す

/-- 概要：P⁰ は E∞ 代数の射で自然。
方針：作用素の作用の自然性。
規約：—
使われ方：Frobenius の自己同型が P⁰ と可換（Δ_perf/p）。 -/
theorem powerOperationZero_natural {X Y : (E.CAlg k) _⦋0⦌} (f : SSet.Edge X Y) (n : ℤ)
    (x : homotopy (E := E) k p X n) :
    homotopyMap (E := E) k p f n (powerOperationZero (E := E) k p X n x) = powerOperationZero (E := E) k p Y n (homotopyMap (E := E) k p f n x) := by
  sorry -- functorCellToNatTrans_app_eq_evaluate と E.restrictD_homologyIso の自然性を
        -- 合成し、n = 0 では E.pi0_forget の自然性で台の H⁰ の環から移す

/-- 概要：P⁰ を忘却 U : CAlg_k → D(k)上の **Frobenius 半線形な coherent 自然変換**として（Lurie DAG XIII Constr 2.2.6 の強さ。W9-II-02）。
方針：界面の半線形自然変換を使う。π_n 上の作用はその成分。
規約：E∞ 代数の射で自然、極限・幾何学的実現の錐と両立。
使われ方：(iii)。 -/
def powerOperationZero_natTrans : FunctorHom (E.forget k)
    (E.forget k ≫ derivedInfinityRestrictScalars (E := E) (frobenius k p)) := E.powerOp0 k p

def powerOperationZero_primeField (p : ℕ) [Fact p.Prime] :
    FunctorHom (E.forget (ZMod p)) (E.forget (ZMod p)) := by
  let U := E.forget (ZMod p)
  have α : FunctorHom U (U ≫ derivedInfinityRestrictScalars (E := E) (RingHom.id (ZMod p))) := by
    simpa only [ZMod.frobenius_zmod] using powerOperationZero_natTrans (E := E) (ZMod p) p
  exact α ≫ ((derivedInfinityRestrictScalars_id (E := E) (S := ZMod p)).precomp U).hom ≫
    eqToHom (by simp)

/-- 係数の読み替えは Hⁱ の台の加法群を変えない。 -/
def restrictHomologyAddEquiv (M : (derivedInfinityCategory k) _⦋0⦌) (i : ℤ) :
    derivedInfinityHomology k i ((derivedInfinityRestrictScalars (E := E) (frobenius k p)).app _ M) ≃+
      derivedInfinityHomology k i M := E.restrictD_homology (frobenius k p) i M

theorem powerOperationZero_component (X : (E.CAlg k) _⦋0⦌) (n : ℤ) (x : homotopy (E := E) k p X n) :
    let U := E.forget k
    let e := Classical.choose (homotopyCategory_homMk_surjective _ _
      (functorHomEvaluate (powerOperationZero_natTrans (E := E) k p) X))
    homotopyCohomology (E := E) k p X n (powerOperationZero (E := E) k p X n x) =
      restrictHomologyAddEquiv (E := E) k p (U.app _ X) (-n)
        ((derivedInfinityHomologyMap k (-n) e) (homotopyCohomology (E := E) k p X n x)) := by
  sorry -- 選んだ辺の類は powerOp0 の評価。加法同型は restrictD_homologyIso の成分

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
    VertexIso (Cosimplicial.totEInfinity (E := E) k (X ⋙ frobeniusRestriction k p))
      ((cAlgRestrictScalars (E := E) (frobenius k p)).app _ (Cosimplicial.totEInfinity (E := E) k X)) := (E.ofCosimplicial_restrict (frobenius k p)).app (nerveVertex X)

/-- 概要：(iii) 離散な可換 k 代数 B では P⁰_{HB} = H(Frob_B)。U が極限と幾何学的実現を保ち P⁰ が coherent な自然変換なので、この同定は
余単体的 Tot_{E∞}(X^•) と単体的実現へ移る：levelwise Frobenius x ↦ x^p が Tot・実現の P⁰ を誘導する。
方針：自然変換の錐との両立（W9-II-02 で訂正：**通常の p 重 cup 積による説明は誤り**。P⁰ は次数を保つが p 重 cup 積は次数 q を pq にする。
S¹ の mod 2 で x ∪ x = 0 だが Frobenius は恒等）。
規約：Shared/CosimplicialEInfinity の `totEInfinity`。
使われ方：Lemma 8.4 (a)：Δ_perf/p の塔の shift が P⁰ と同じ作用を誘導する（G-A3-9 の模型の φ との比較と合わせて）。 -/
theorem powerOperationZero_eq_frobenius_discrete (B : A_R k) :
    let X := (E.discrete k).app _ (nerveVertex B)
    let U := E.forget k
    let f := (nerve.edgeMk (discreteFrobenius k p B)).map (E.discrete k ≫ U)
    functorHomEvaluate (powerOperationZero_natTrans (E := E) k p) X =
      Truncated.HomotopyCategory.homMk f.toTruncated ≫
        ((cAlgRestrictScalars_algebraEmbedding (E := E) (frobenius k p) B).map U).hom ≫
        ((cAlgRestrictScalars_forget (E := E) (frobenius k p)).app X).hom := E.powerOp0_discrete k p B (discreteFrobenius k p B) (fun _ => rfl)

theorem powerOperationZero_eq_frobenius_tot (X : Cosimplicial.CosimplicialAlgebra k) :
    let T := Cosimplicial.totEInfinity (E := E) k X
    let U := E.forget k
    let f := (Cosimplicial.totEInfinity_map (E := E) k (cosimplicialFrobenius k p X)).map U
    functorHomEvaluate (powerOperationZero_natTrans (E := E) k p) T =
      Truncated.HomotopyCategory.homMk f.toTruncated ≫ ((totRestrictFrobeniusIso (E := E) k p X).map U).hom ≫
        ((cAlgRestrictScalars_forget (E := E) (frobenius k p)).app T).hom := E.powerOp0_tot k p X (cosimplicialFrobenius k p X) (fun _ _ => rfl)

end SerrePositivity.EInfinity
