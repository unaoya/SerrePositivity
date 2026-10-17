module

public import SerrePositivity.BhattScholze.Andre.MonicFamilyFiniteSystem

/-!
# André E1・E2：全族の通常根商と有限部分族の余極限

## 概要

任意多項式族の通常根商を有限部分族の通常商の R 代数余極限と同定する。
BS 著者版 Thm 7.14（p.61）、Rem 7.15（p.62）の任意同時根添加の通常代数部分である。

## 方針

各根を一元集合の段から余極限へ写し、根族商の普遍射を用いて逆射を作る。
有限段の生成元で両立性と相互逆性を確認する。

## 規約

モニック性・正次数・遷移射の単射性を仮定しない。
有向余極限の自由性はこの同型からは主張しない。

## 使われ方

有限モニック族の通常忠実平坦性を全族の実際の関係商へ移す。
-/

@[expose] public noncomputable section

universe u v

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {R : Type u} [CommRing R] {σ : Type v} (f : σ → Polynomial R)

local notation "S" => (fun T : Finset σ => PolynomialFamilyFiniteStage f T)
local notation "d" => (fun (i : Finset σ) (j : Finset σ) (h : i ≤ j) =>
  polynomialFamilyFiniteMap f h)

/-- 概要：有限部分族の通常商の標準 R 代数余極限。
方針：前工程で構成した有向系に Mathlib の DirectLimit を適用する。
規約：元の係数作用を保持する。
使われ方：BS Thm 7.14（著者版 p.61）の任意族の通常根添加。 -/
abbrev PolynomialFamilyColimit := _root_.DirectLimit S d

/-- 概要：各有限商から通常根族余極限への標準代数射。
方針：Mathlib の標準構造射を使う。
規約：遷移射と同じ R 係数作用。
使われ方：BS Rem 7.15（著者版 p.62）の有限段からの根の像。 -/
def polynomialFamilyColimitOf (T : Finset σ) :
    PolynomialFamilyFiniteStage f T →ₐ[R] PolynomialFamilyColimit f :=
  DirectLimit.Algebra.of S d T

/-- 概要：余極限への構造射は有限段の遷移射と両立する。
方針：DirectLimit の構造射の関係式を使う。
規約：包含の単射性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の根の段への依存を除く。 -/
theorem polynomialFamilyColimitOf_compatible {T U : Finset σ} (h : T ⊆ U)
    (x : PolynomialFamilyFiniteStage f T) :
    polynomialFamilyColimitOf f U (polynomialFamilyFiniteMap f h x) =
      polynomialFamilyColimitOf f T x :=
  DirectLimit.Algebra.of_f h x

/-- 概要：全族の各根をその一元部分族から余極限に入れる。
方針：対応する一元集合の有限商の標準根を写す。
規約：古典的な有限集合の所属判定を使用する。
使われ方：BS Thm 7.14（著者版 p.61）の全族商から余極限への逆射。 -/
def polynomialFamilyColimitRoot (s : σ) : PolynomialFamilyColimit f := by
  classical
  exact polynomialFamilyColimitOf f {s}
    (polynomialFamilyQuotientRoot (fun t : ({s} : Finset σ) => f t)
      ⟨s, Finset.mem_singleton_self (s : σ)⟩)

/-- 概要：有限段の標準根の余極限像は一元段で選んだ同じ根と一致する。
方針：一元集合の元の有限段への包含と遷移射の根公式を使う。
規約：任意の根を含む有限段で計算できる。
使われ方：BS Rem 7.15（著者版 p.62）の全族商と余極限の相互逆性。 -/
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
使われ方：BS Thm 7.14（著者版 p.61）の全族商からの普遍射を作る。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の通常余極限の比較。 -/
def polynomialFamilyColimitToFull : PolynomialFamilyColimit f →ₐ[R] PolynomialFamilyQuotient f :=
  DirectLimit.Algebra.lift S d (PolynomialFamilyQuotient f)
    (polynomialFamilyFiniteToFull f)
    (fun _ _ h x => DFunLike.congr_fun (polynomialFamilyFiniteToFull_compatible f h) x)

/-- 概要：余極限から全族商への射は各有限段の標準射を延長する。
方針：DirectLimit の持ち上げの構造射上の公式。
規約：代数射の等式として述べる。
使われ方：BS Thm 7.14（著者版 p.61）の全族商比較の相互逆性。 -/
theorem polynomialFamilyColimitToFull_comp_of (T : Finset σ) :
    (polynomialFamilyColimitToFull f).comp (polynomialFamilyColimitOf f T) =
      polynomialFamilyFiniteToFull f T := rfl

/-- 概要：全族の通常関係商から有限商余極限への代数射。
方針：余極限の根方程式を根族商の普遍射に渡す。
規約：元の係数作用を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の標準余極限比較の逆射。 -/
def polynomialFamilyFullToColimit : PolynomialFamilyQuotient f →ₐ[R] PolynomialFamilyColimit f :=
  polynomialFamilyQuotientLiftAlgHom f (polynomialFamilyColimitRoot f)
    (polynomialFamilyColimit_eval f)

/-- 概要：全族商から余極限への射は各標準根を余極限の対応する根へ送る。
方針：根族商の普遍射の根公式を使う。
規約：指定根の証明を明示する。
使われ方：BS Thm 7.14（著者版 p.61）の全族商比較の生成元計算。 -/
theorem polynomialFamilyFullToColimit_root (s : σ) :
    polynomialFamilyFullToColimit f (polynomialFamilyQuotientRoot f s) =
      polynomialFamilyColimitRoot f s :=
  polynomialFamilyQuotientLift_root f _ _ (polynomialFamilyColimit_eval f) s

/-- 概要：全族商を経由する余極限への有限段の射は標準構造射と一致する。
方針：有限商の各標準根の像を比較する。
規約：有限段からの代数射の等式。
使われ方：BS Rem 7.15（著者版 p.62）の余極限側の相互逆性。 -/
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
使われ方：BS Thm 7.14（著者版 p.61）の通常忠実平坦性を任意族の実商へ移す。 -/
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
