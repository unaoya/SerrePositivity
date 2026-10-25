module

public import SerrePositivity.BhattScholze.Andre.Remark715.DeltaDivisionWittEvaluation

/-!
# André E1・E2：raw 二元剰余の Witt 普遍性

## 概要

A{b/c}/(p,d) の係数射と Witt 点、その通常環射への普遍性を明示する。
BS Rem 7.15（著者版 p.62）の分母の違う raw 剰余を比較するための入口。

## 方針

Witt 解からの通常環射を、p と d を殺す条件により二元商へ降ろす。

## 規約

剰余環の非零性・δ 構造・正則性を要求しない。
原典とは異なる具体的 Witt 座標による通常商の比較を行う。

## 使われ方

分母 φ(d) と p の raw 剰余同士に比較射を構成する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A B C σ : Type u} [CommRing A] [CommRing B] [CommRing C]
variable (D : DeltaStructure p A) (c : A) (b : σ → A) (d : A)
local notation "Raw" => DeltaAdjoinDivision D c b
local notation "j" => deltaAdjoinDivisionMap D c b

/-- 概要：raw 除算包を係数の p,d で割る通常商環。
方針：二元生成イデアルの商を取る。
規約：c と d は一致しなくてもよい。
使われ方：BS Rem 7.15（著者版 p.62）の未完備二元剰余。 -/
abbrev DeltaDivisionPairResidue := Raw ⧸ Ideal.span {(p : Raw), j d}

/-- 概要：二元剰余への標準係数射。
方針：raw の係数射と商射を合成する。
規約：元の A 係数を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の剰余比較の係数作用。 -/
def deltaDivisionPairResidueBase : A →+* DeltaDivisionPairResidue D c b d :=
  (Ideal.Quotient.mk _).comp j

/-- 概要：raw 二元剰余では p が零。
方針：p の生成イデアルへの所属を使う。
規約：零環も許す。
使われ方：BS Rem 7.15（著者版 p.62）の Witt 分母正規化の入力。 -/
theorem deltaDivisionPairResidue_prime_zero : (p : DeltaDivisionPairResidue D c b d) = 0 := by
  have h : (Ideal.Quotient.mk (Ideal.span {(p : Raw), j d})) (p : Raw) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa only [map_natCast] using h

/-- 概要：二元剰余の標準係数射は d を殺す。
方針：d の像が生成イデアルに属すことを使う。
規約：除算分母 c とは別に指定した d の消滅。
使われ方：BS Rem 7.15（著者版 p.62）の単元倍分母公式。 -/
theorem deltaDivisionPairResidueBase_d : deltaDivisionPairResidueBase D c b d d = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/-- 概要：二元剰余の標準 Witt 点。
方針：raw Witt 点を通常商射で送る。
規約：全ての Witt 座標を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の比較射の生成元。 -/
def deltaDivisionPairResiduePoint (s : σ) : WittVector p (DeltaDivisionPairResidue D c b d) :=
  WittVector.map (Ideal.Quotient.mk _) (deltaDivisionRawWittPoint D c b s)

/-- 概要：Witt ベクトルの通常環射での像は環射の合成と可換。
方針：各係数で定義を確認する。
規約：δ 構造を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の Witt 点の逆合成の計算。 -/
theorem witt_map_comp_apply (F : B →+* C) (G : A →+* B) (v : WittVector p A) :
    WittVector.map F (WittVector.map G v) = WittVector.map (F.comp G) v := by
  ext n
  rfl

variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))

include hpA hgL in
/-- 概要：二元剰余の Witt 点は元の全除算方程式を満たす。
方針：raw Witt 点の方程式を商射で送る。
規約：源の p 正則性だけを仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の分母変換に供給する具体的解。 -/
theorem deltaDivisionPairResiduePoint_relation (s : σ) :
    WittVector.map (deltaDivisionPairResidueBase D c b d) (deltaWittGhostVector D c) *
        deltaDivisionPairResiduePoint D c b d s =
      WittVector.map (deltaDivisionPairResidueBase D c b d) (deltaWittGhostVector D (b s)) := by
  have h := congrArg (WittVector.map (Ideal.Quotient.mk (Ideal.span {(p : Raw), j d})))
    (deltaDivisionRawWittPoint_relation D hpA c b hgL s)
  simpa only [map_mul, witt_map_comp_apply, deltaDivisionPairResidueBase,
    deltaDivisionPairResiduePoint] using h

variable (q : A →+* B) (w : σ → WittVector p B)
variable (hpB : (p : B) = 0) (hqd : q d = 0)
variable (hw : ∀ s, WittVector.map q (deltaWittGhostVector D c) * w s =
  WittVector.map q (deltaWittGhostVector D (b s)))

/-- 概要：p,d を殺す係数射と Witt 解から二元剰余への通常環射を作る。
方針：Witt 解の raw 評価が二元イデアルを殺すことを確認する。
規約：終域に δ 構造や非零性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の raw 剰余比較の両方向の射。 -/
def deltaDivisionPairResidueLift : DeltaDivisionPairResidue D c b d →+* B := by
  let F := deltaDivisionWittMap D hpA q w c b hgL hw
  apply Ideal.Quotient.lift _ F
  have hker : Ideal.span {(p : Raw), j d} ≤ RingHom.ker F := by
    apply Ideal.span_le.mpr
    intro r hr
    rcases Set.mem_insert_iff.mp hr with hr | hr
    · subst r
      change F (p : Raw) = 0
      rw [map_natCast]
      exact hpB
    · have hr' : r = j d := Set.mem_singleton_iff.mp hr
      subst r
      change deltaDivisionWittMap D hpA q w c b hgL hw (j d) = 0
      rw [deltaDivisionWittMap_coeff]
      exact hqd
  exact fun r hr => hker hr

/-- 概要：二元剰余からの射は元の係数射を保つ。
方針：商に降ろす前の raw 評価の係数公式を使う。
規約：全ての A の元に対して述べる。
使われ方：BS Rem 7.15（著者版 p.62）の係数を保つ比較。 -/
theorem deltaDivisionPairResidueLift_base (r : A) :
    deltaDivisionPairResidueLift D c b d hpA hgL q w hpB hqd hw
      (deltaDivisionPairResidueBase D c b d r) = q r :=
  deltaDivisionWittMap_coeff D hpA q w c b hgL hw r

/-- 概要：二元剰余からの射は指定した全 Witt 解を保つ。
方針：各係数で raw 評価の Witt 点公式を使う。
規約：通常環射の Witt ベクトル写像で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の変数変換を確認する公式。 -/
theorem deltaDivisionPairResidueLift_point (s : σ) :
    WittVector.map (deltaDivisionPairResidueLift D c b d hpA hgL q w hpB hqd hw)
      (deltaDivisionPairResiduePoint D c b d s) = w s := by
  ext n
  exact congrArg (fun z : WittVector p B => z.coeff n)
    (deltaDivisionWittMap_point D hpA q w c b hgL hw s)

include hpA in
/-- 概要：二元剰余の通常環射は係数と全 Witt 点で決まる。
方針：商射の全射性と raw 包の Witt 外延性を使う。
規約：二つの通常環射に δ 互換性を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の二つの剰余比較射の両逆合成。 -/
theorem deltaDivisionPairResidueRingHom_ext (f g : DeltaDivisionPairResidue D c b d →+* B)
    (hc : ∀ r, f (deltaDivisionPairResidueBase D c b d r) =
      g (deltaDivisionPairResidueBase D c b d r))
    (hw : ∀ s, WittVector.map f (deltaDivisionPairResiduePoint D c b d s) =
      WittVector.map g (deltaDivisionPairResiduePoint D c b d s)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply deltaDivisionRingHom_ext_of_wittPoint D hpA c b
  · exact hc
  · intro s
    simpa only [← witt_map_comp_apply, deltaDivisionPairResiduePoint] using hw s

end SerrePositivity.BhattScholze.Andre
