module

public import SerrePositivity.BhattScholze.Andre.MonicFamilyQuotientUniversal
public import Mathlib.Algebra.Colimit.DirectLimit

/-!
# André E1・E2：通常根族商の有限部分族有向系

## 概要

任意の多項式族の有限部分族の通常商と、包含に沿う根を保つ標準遷移射を構成する。
BS 著者版 Thm 7.14（p.61）、Rem 7.15（p.62）の任意族の通常根添加の準備。

## 方針

各有限商の普遍射を用い、係数と標準根上で恒等性・合成則を確認する。
Mathlib の R 代数有向系として構成し、余極限で元の係数作用を保持する。

## 規約

モニック性・正次数はこの有向系の構成には不要。
遷移射の単射性や完備性も仮定しない。

## 使われ方

全族の通常商と有限商余極限の比較、および通常忠実平坦性の有限部分族からの移送。
-/

@[expose] public noncomputable section

universe u v w

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：標準係数作用の根族商から指定根を持つ R 代数への普遍代数射。
方針：既存の普遍環射に係数を保つ性質を付ける。
規約：指定根方程式だけを要求する。
使われ方：BS Thm 7.14（著者版 p.61）の通常有限商の遷移射。 -/
def polynomialFamilyQuotientLiftAlgHom {R : Type u} [CommRing R] {σ : Type v}
    {S : Type w} [CommRing S] [Algebra R S] (f : σ → Polynomial R) (a : σ → S)
    (ha : ∀ s, (f s).eval₂ (algebraMap R S) (a s) = 0) :
    PolynomialFamilyQuotient f →ₐ[R] S :=
  { polynomialFamilyQuotientLift f (algebraMap R S) a ha with
    commutes' := polynomialFamilyQuotientLift_coeff f _ a ha }

/-- 概要：根族商からの代数射は標準根上の値で一意に決まる。
方針：係数上の一致は代数射性から供給し、環射の外延性を適用する。
規約：元の R 係数作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の遷移射の合成則の検証。 -/
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
使われ方：BS Thm 7.14（著者版 p.61）の任意同時根添加の有限段。 -/
abbrev PolynomialFamilyFiniteStage (T : Finset σ) :=
  PolynomialFamilyQuotient (fun s : T => f s)

/-- 概要：有限部分族の包含は標準根を対応する標準根へ送る代数射を与える。
方針：商の普遍代数射に終域の標準根を指定する。
規約：係数作用を変えない。
使われ方：BS Rem 7.15（著者版 p.62）の有限部分族有向系。 -/
def polynomialFamilyFiniteMap {S T : Finset σ} (h : S ⊆ T) :
    PolynomialFamilyFiniteStage f S →ₐ[R] PolynomialFamilyFiniteStage f T :=
  polynomialFamilyQuotientLiftAlgHom (fun s : S => f s)
    (fun s => polynomialFamilyQuotientRoot (fun t : T => f t) ⟨s, h s.property⟩)
    (fun s => polynomialFamilyQuotient_eval (fun t : T => f t) ⟨s, h s.property⟩)

/-- 概要：有限部分族の遷移射は指定根を保持する。
方針：商の普遍射の根上の公式を適用する。
規約：包含の証明の違いは部分型の証明無関係性で吸収する。
使われ方：BS Thm 7.14（著者版 p.61）の任意族の根の追跡。 -/
theorem polynomialFamilyFiniteMap_root {S T : Finset σ} (h : S ⊆ T) (s : S) :
    polynomialFamilyFiniteMap f h (polynomialFamilyQuotientRoot (fun t : S => f t) s) =
      polynomialFamilyQuotientRoot (fun t : T => f t) ⟨s, h s.property⟩ :=
  polynomialFamilyQuotientLift_root _ _ _
    (fun s : S => polynomialFamilyQuotient_eval (fun t : T => f t) ⟨s, h s.property⟩) s

/-- 概要：同じ有限部分族への恒等包含の遷移射は恒等代数射。
方針：標準根上の値を比較する。
規約：係数上の一致は代数射性による。
使われ方：BS Rem 7.15（著者版 p.62）の有向系の恒等則。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の有向系の合成則。 -/
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
使われ方：BS Thm 7.14（著者版 p.61）の任意族の通常商の余極限。 -/
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
使われ方：BS Thm 7.14（著者版 p.61）の全族商と余極限の比較。 -/
def polynomialFamilyFiniteToFull (T : Finset σ) :
    PolynomialFamilyFiniteStage f T →ₐ[R] PolynomialFamilyQuotient f :=
  polynomialFamilyQuotientLiftAlgHom (fun t : T => f t)
    (fun t => polynomialFamilyQuotientRoot f t) (fun t => polynomialFamilyQuotient_eval f t)

/-- 概要：有限段から全族商への標準射は根を保持する。
方針：商の普遍射の根公式を適用する。
規約：標準根の添字は元の添字への包含で比較する。
使われ方：BS Rem 7.15（著者版 p.62）の全族の根の追跡。 -/
theorem polynomialFamilyFiniteToFull_root (T : Finset σ) (t : T) :
    polynomialFamilyFiniteToFull f T (polynomialFamilyQuotientRoot (fun s : T => f s) t) =
      polynomialFamilyQuotientRoot f t :=
  polynomialFamilyQuotientLift_root _ _ _ (fun s : T => polynomialFamilyQuotient_eval f s) t

/-- 概要：全族商への標準射は有限部分族の全遷移と両立する。
方針：標準根の値で両辺を比較する。
規約：有限部分族の包含は任意。
使われ方：BS Rem 7.15（著者版 p.62）の余極限から全族商への標準射。 -/
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
