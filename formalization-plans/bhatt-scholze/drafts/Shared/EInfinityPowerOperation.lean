-- 将来の置き場所：SerrePositivity.EInfinity.PowerOperation.*（新設、BarrattEccles・Operad の隣。調整役の決定、main 431c40741、M14。担当は A4 の中身を書く段階で決める）
-- 設計書：formalization-plans/bhatt-scholze/a4-design.md G-A4-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.EInfinity.Interface.PowerOperation
public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import Mathlib.FieldTheory.Finite.Basic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Homology
-- 取り込み時の依存先：drafts/DerivedGeneral/ScalarRestriction.lean。
-- 本ファイルは drafts/Shared/CosimplicialEInfinity.lean（余単体的可換環の Tot_{E∞}）を使う。

/-!
# E∞-F_p 代数の冪作用 P⁰（[Lur11, §2.2]、Berger–Fresse、May）

## 概要
標数 p の E∞ 代数のホモトピー π_* に作用する冪作用のうち P⁰ を定義し、
(i) π_0 では Frobenius x ↦ x^p、(ii) π_n（n > 0、ホモロジー的）では零（[Lur11, Rem 2.2.7]）、(iii) 余単体的（および単体的余単体的）可換 F_p 代数の
levelwise Frobenius x ↦ x^p が Tot_{E∞}（実現）の P⁰ を誘導すること、を述べる。

## 方針
May の P⁰ を ho(CAlg F_p) 上の可換群値の自然変換として界面から読む。
一般の k は素体への係数制限とホモロジーの自然同型で共役する。
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
方針：本欄を素体へ制限し、ho(CAlg) 上の全整数次数の加法的演算を共役する。
規約：k 線形ではない（φ_k 半線形）。
使われ方：Lemma 8.4。
 -/
def powerOperationZero (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (X : (E.CAlg k) _⦋0⦌) (n : ℤ) : homotopy (E := E) k p X n →+ homotopy (E := E) k p X n := by
  let α := (E.powerOp0Over k p n).app (SSet.HomotopyCategory.mk X)
  exact (homotopyCohomology (E := E) k p X n).symm.toAddMonoidHom.comp
    (α.hom.comp (homotopyCohomology (E := E) k p X n).toAddMonoidHom)

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
  sorry -- E.powerOp0Over の NatTrans の自然性と E.restrictD_homologyIso の自然性を
        -- 合成し、n = 0 では E.pi0_forget の自然性で台の H⁰ の環から移す

/-!
D79 改訂：powerOperationZero_natTrans・powerOperationZero_primeField の coherent な
Sp 値の出力、および powerOperationZero_component の強い成分比較は補完へ回す。
このファイルでは作らず、ho(CAlg) 上の可換群の演算と辺に沿う自然性だけを使う。
-/

/-- 係数の読み替えは Hⁱ の台の加法群を変えない。 -/
def restrictHomologyAddEquiv (M : (derivedInfinityCategory k) _⦋0⦌) (i : ℤ) :
    derivedInfinityHomology k i ((derivedInfinityRestrictScalars (E := E) (frobenius k p)).app _ M) ≃+
      derivedInfinityHomology k i M := E.restrictD_homology (frobenius k p) i M

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

/-- 離散な可換 k 代数では、全整数次数で P⁰ が Frobenius を誘導する。
素体の本欄から係数制限で運ぶ。Sp 値の辺の等式は主張しない。 -/
theorem powerOperationZero_eq_frobenius_discrete (B : A_R k) (n : ℤ) :
    let X := (E.discrete k).app _ (nerveVertex B)
    let U := E.forget k
    let f := (nerve.edgeMk (discreteFrobenius k p B)).map (E.discrete k ≫ U)
    (E.powerOp0Over k p n).app (SSet.HomotopyCategory.mk X) =
      (additiveCohomologyOnHo k (-n)).map
        (Truncated.HomotopyCategory.homMk f.toTruncated ≫
          ((cAlgRestrictScalars_algebraEmbedding (E := E) (frobenius k p) B).map U).hom ≫
            ((cAlgRestrictScalars_forget (E := E) (frobenius k p)).app X).hom) ≫
        (E.restrictD_homologyIso (frobenius k p) (-n)).hom.app
          (SSet.HomotopyCategory.mk (atVertex U X)) := by
  sorry -- E.powerOp0_discrete と discrete_restrict、restrictD_homologyIso で共役する。

/-- Tot の全整数次数で、levelwise Frobenius が同じ P⁰ を誘導する。
May の top operation の比較を使う。一般の実現との可換性はこの欄からは推論しない。 -/
theorem powerOperationZero_eq_frobenius_tot (X : Cosimplicial.CosimplicialAlgebra k) (n : ℤ) :
    let T := Cosimplicial.totEInfinity (E := E) k X
    let U := E.forget k
    let f := (Cosimplicial.totEInfinity_map (E := E) k (cosimplicialFrobenius k p X)).map U
    (E.powerOp0Over k p n).app (SSet.HomotopyCategory.mk T) =
      (additiveCohomologyOnHo k (-n)).map
        (Truncated.HomotopyCategory.homMk f.toTruncated ≫
          ((totRestrictFrobeniusIso (E := E) k p X).map U).hom ≫
            ((cAlgRestrictScalars_forget (E := E) (frobenius k p)).app T).hom) ≫
        (E.restrictD_homologyIso (frobenius k p) (-n)).hom.app
          (SSet.HomotopyCategory.mk (atVertex U T)) := by
  sorry -- E.powerOp0_tot と ofCosimplicial_restrict、restrictD_homologyIso で共役する。

end SerrePositivity.EInfinity
