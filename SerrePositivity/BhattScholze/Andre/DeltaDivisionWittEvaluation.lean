module

public import SerrePositivity.BhattScholze.DeltaPDivisionWittResidueEvaluation

/-!
# André E1・E2：任意の Witt 解から raw δ 除算包への通常環射

## 概要

W(d)w_s=W(a_s) を満たす任意の Witt 点から A{a/d} への通常評価を作る。
BS Rem 7.15（著者版 p.62）の分母正規化に使う。

## 方針

既存の逆 Witt 座標と jet 消滅比較を使って、全 δ 関係を殺す。

## 規約

源の p 正則性と ghost 射の単射性を明示し、終域の δ 構造は要求しない。
原典とは異なる通常環射による具体的比較である。

## 使われ方

Witt 解の単元倍による変数変換を raw 包の通常環射へ移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A B σ : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (q : A →+* B) (w : σ → WittVector p B)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "F₀" => relativeFreeDeltaStructure σ D

/-- 概要：任意の Witt 点の全係数を自由 δ 環の逆 Witt 座標へ代入する。
方針：逆 Witt 座標の通常多項式評価を合成する。
規約：終域の δ 構造は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
def deltaDivisionWittEval : L₀ →+* B :=
  (MvPolynomial.eval₂Hom q (fun z : σ × ℕ ↦
    (w z.1).coeff z.2)).comp
      (relativeFreeWittInverseMap D hpA).toRingHom

/-- 概要：Witt 点による通常評価は元の係数射を保つ。
方針：逆座標の係数公式を使う。
規約：終域の δ 構造は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittEval_C (r : A) :
    deltaDivisionWittEval D hpA q w (MvPolynomial.C r) = q r := by
  change MvPolynomial.eval₂Hom q _
    (relativeFreeWittInverseMap D hpA (MvPolynomial.C r)) = _
  rw [show relativeFreeWittInverseMap D hpA (MvPolynomial.C r) = MvPolynomial.C r from
    AlgHom.commutes (relativeFreeWittInverseMap D hpA) r, MvPolynomial.eval₂Hom_C]

/-- 概要：自由変数の各 Witt 係数は指定した点の同じ係数へ送られる。
方針：逆座標の変数公式を使う。
規約：終域の δ 構造は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittEval_coefficient (s : σ) (n : ℕ) :
    deltaDivisionWittEval D hpA q w (relativeFreeWittGhostCoefficient D s n) =
      (w s).coeff n := by
  change MvPolynomial.eval₂Hom q _
    (relativeFreeWittInverseMap D hpA (relativeFreeWittGhostCoefficient D s n)) = _
  rw [relativeFreeWittInverseMap_coefficient, MvPolynomial.eval₂Hom_X']

/-- 概要：自由初期変数の全 Witt 元は指定した点へ送られる。
方針：各係数で評価の公式を使う。
規約：終域の δ 構造は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittEval_witt_X (s : σ) :
    WittVector.map (deltaDivisionWittEval D hpA q w)
      (deltaWittGhostVector F₀ (MvPolynomial.X (s, 0))) =
        w s := by
  ext n
  rw [WittVector.map_coeff]
  exact deltaDivisionWittEval_coefficient D hpA q w s n

/-- 概要：基底の全 Witt 元は元の通常係数射で送られる。
方針：自由 δ 構造の係数自然性を使う。
規約：終域の δ 構造は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittEval_witt_C
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀)) (r : A) :
    WittVector.map (deltaDivisionWittEval D hpA q w)
      (deltaWittGhostVector F₀ (MvPolynomial.C r)) =
        WittVector.map q (deltaWittGhostVector D r) := by
  ext n
  rw [WittVector.map_coeff, deltaWittGhostVector_relativeFree_C_coeff D hgL,
    deltaDivisionWittEval_C, WittVector.map_coeff]

/-- 概要：Witt 除算方程式を満たす点は初期関係の全 Witt 元を殺す。
方針：Witt 環射の乗法性と指定した方程式を使う。
規約：終域の δ 構造は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittEval_kills_witt_relation (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hw : ∀ s, WittVector.map q (deltaWittGhostVector D d) * w s =
      WittVector.map q (deltaWittGhostVector D (a s))) (s : σ) :
    WittVector.map (deltaDivisionWittEval D hpA q w)
      (deltaWittGhostVector F₀ (MvPolynomial.C d * MvPolynomial.X (s, 0) -
        MvPolynomial.C (a s))) = 0 := by
  change WittVector.map (deltaDivisionWittEval D hpA q w)
    (deltaWittGhostRingHom F₀ hgL (MvPolynomial.C d * MvPolynomial.X (s, 0) -
      MvPolynomial.C (a s))) = 0
  rw [map_sub, map_mul, map_sub, map_mul]
  change WittVector.map (deltaDivisionWittEval D hpA q w)
      (deltaWittGhostVector F₀ (MvPolynomial.C d)) *
    WittVector.map (deltaDivisionWittEval D hpA q w)
      (deltaWittGhostVector F₀ (MvPolynomial.X (s, 0))) -
    WittVector.map (deltaDivisionWittEval D hpA q w)
      (deltaWittGhostVector F₀ (MvPolynomial.C (a s))) = 0
  rw [deltaDivisionWittEval_witt_C D hpA q w hgL,
    deltaDivisionWittEval_witt_X, deltaDivisionWittEval_witt_C D hpA q w hgL]
  exact sub_eq_zero.mpr (hw s)

/-- 概要：Witt 解の通常評価は実除算関係の全 δ 反復を殺す。
方針：Witt 係数の消滅を既存の jet 比較で移す。
規約：終域の δ 構造は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittEval_kills_iterated_relation (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hw : ∀ s, WittVector.map q (deltaWittGhostVector D d) * w s =
      WittVector.map q (deltaWittGhostVector D (a s))) (s : σ) (n : ℕ) :
    deltaDivisionWittEval D hpA q w
      (deltaDivisionIteratedRelation D d a s n) = 0 := by
  have hpL : Function.Injective (fun x : L₀ ↦ (p : L₀) * x) := by
    have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
    have h' : IsSMulRegular L₀ (p : L₀) := by simpa only [map_natCast] using h
    intro x z hxz
    apply h'
    simpa only [smul_eq_mul] using hxz
  have hw := deltaDivisionWittEval_kills_witt_relation D hpA q w d a hgL hw s
  have hc : ∀ i ≤ n, deltaDivisionWittEval D hpA q w
      ((deltaWittGhostVector F₀ (MvPolynomial.C d * MvPolynomial.X (s, 0) -
        MvPolynomial.C (a s))).coeff i) = 0 := by
    intro i _
    have h := congrArg (fun w : WittVector p B ↦ w.coeff i) hw
    simpa only [WittVector.map_coeff, WittVector.zero_coeff] using h
  have hj := (deltaWittGhostVector_jets_zero_iff F₀ hpL hgL
    (deltaDivisionWittEval D hpA q w)
    (MvPolynomial.C d * MvPolynomial.X (s, 0) -
      MvPolynomial.C (a s)) n).mpr hc
  exact hj n le_rfl

/-- 概要：任意の Witt 解から raw δ 除算包への通常環射を構成する。
方針：全 δ 反復関係を殺す通常評価を商へ降ろす。
規約：終域の δ 構造は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
def deltaDivisionWittMap (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hw : ∀ s, WittVector.map q (deltaWittGhostVector D d) * w s =
      WittVector.map q (deltaWittGhostVector D (a s))) : DeltaAdjoinDivision D d a →+* B :=
  deltaDivisionIteratedRelationsLift D d a (deltaDivisionWittEval D hpA q w)
    (deltaDivisionWittEval_kills_iterated_relation D hpA q w d a hgL hw)

/-- 概要：構成した射は自由環上の指定した評価を延長する。
方針：商射の定義を使う。
規約：終域の δ 構造は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittMap_comp_mk (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hw : ∀ s, WittVector.map q (deltaWittGhostVector D d) * w s =
      WittVector.map q (deltaWittGhostVector D (a s))) :
    (deltaDivisionWittMap D hpA q w d a hgL hw).comp
      (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal d a))) = deltaDivisionWittEval D hpA q w := rfl

/-- 概要：構成した raw 包の射は元の係数射を保つ。
方針：自由環上の係数公式を使う。
規約：終域の δ 構造は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の分母正規化と pd 包比較。 -/
theorem deltaDivisionWittMap_coeff (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hw : ∀ s, WittVector.map q (deltaWittGhostVector D d) * w s =
      WittVector.map q (deltaWittGhostVector D (a s))) (r : A) :
    deltaDivisionWittMap D hpA q w d a hgL hw
      (deltaAdjoinDivisionMap D d a r) = q r :=
  deltaDivisionWittEval_C D hpA q w r


/-- 概要：raw 包の各自由変数の全 Witt 座標を通常商射で送った点。
方針：自由 δ 環上の Witt 元をそのまま raw 商へ送る。
規約：raw 包の δ 構造や終域の正則性を使わない定義。
使われ方：BS Rem 7.15（著者版 p.62）の通常比較射の生成元。 -/
def deltaDivisionRawWittPoint (d : A) (a : σ → A) (s : σ) :
    WittVector p (DeltaAdjoinDivision D d a) :=
  WittVector.map (Ideal.Quotient.mk _)
    (deltaWittGhostVector F₀ (MvPolynomial.X (s, 0)))

/-- 概要：Witt 解から作った通常射は raw Witt 点を指定した解へ送る。
方針：各係数で自由環の評価公式を使う。
規約：全ての添字 s の全 Witt 係数を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の単元変換で作る射の逆合成。 -/
theorem deltaDivisionWittMap_point (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hw : ∀ s, WittVector.map q (deltaWittGhostVector D d) * w s =
      WittVector.map q (deltaWittGhostVector D (a s))) (s : σ) :
    WittVector.map (deltaDivisionWittMap D hpA q w d a hgL hw)
      (deltaDivisionRawWittPoint D d a s) = w s := by
  ext n
  change deltaDivisionWittEval D hpA q w (relativeFreeWittGhostCoefficient D s n) = _
  exact deltaDivisionWittEval_coefficient D hpA q w s n

include hpA in
/-- 概要：raw 包の通常環射は元の係数と全 raw Witt 点で決まる。
方針：商射の全射性と可逆な Witt 座標変換で多項式の外延性へ帰着する。
規約：比較する射には δ 互換性を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の raw 剰余比較の両逆合成。 -/
theorem deltaDivisionRingHom_ext_of_wittPoint (d : A) (a : σ → A)
    (f g : DeltaAdjoinDivision D d a →+* B)
    (hc : ∀ r, f (deltaAdjoinDivisionMap D d a r) =
      g (deltaAdjoinDivisionMap D d a r))
    (hw : ∀ s, WittVector.map f (deltaDivisionRawWittPoint D d a s) =
      WittVector.map g (deltaDivisionRawWittPoint D d a s)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  have he : (f.comp (Ideal.Quotient.mk _)).comp
        (relativeFreeWittCoordinateEquiv D hpA).toRingHom =
      (g.comp (Ideal.Quotient.mk _)).comp
        (relativeFreeWittCoordinateEquiv D hpA).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change f (Ideal.Quotient.mk _ (relativeFreeWittCoordinateEquiv D hpA
          (MvPolynomial.C r))) =
        g (Ideal.Quotient.mk _ (relativeFreeWittCoordinateEquiv D hpA (MvPolynomial.C r)))
      rw [show relativeFreeWittCoordinateEquiv D hpA (MvPolynomial.C r) =
        MvPolynomial.C r from AlgEquiv.commutes (relativeFreeWittCoordinateEquiv D hpA) r]
      exact hc r
    · intro sn
      obtain ⟨s, n⟩ := sn
      change f (Ideal.Quotient.mk _ (relativeFreeWittCoordinateEquiv D hpA
          (MvPolynomial.X (s, n)))) =
        g (Ideal.Quotient.mk _ (relativeFreeWittCoordinateEquiv D hpA (MvPolynomial.X (s, n))))
      rw [relativeFreeWittCoordinateEquiv_X]
      have h := congrArg (fun z : WittVector p B => z.coeff n) (hw s)
      simpa only [deltaDivisionRawWittPoint, WittVector.map_coeff,
        relativeFreeWittGhostCoefficient] using h
  apply RingHom.ext
  intro r
  obtain ⟨t, rfl⟩ := (relativeFreeWittCoordinateEquiv D hpA).surjective r
  exact RingHom.congr_fun he t

include hpA in
/-- 概要：raw Witt 点は元の全 Witt 除算方程式を満たす。
方針：通常商での全 δ 反復関係の消滅を Witt 係数の消滅へ戻す。
規約：raw 包の p 正則性は仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の raw 包同士の変数変換の入力。 -/
theorem deltaDivisionRawWittPoint_relation (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀)) (s : σ) :
    WittVector.map (deltaAdjoinDivisionMap D d a) (deltaWittGhostVector D d) *
        deltaDivisionRawWittPoint D d a s =
      WittVector.map (deltaAdjoinDivisionMap D d a) (deltaWittGhostVector D (a s)) := by
  let j : L₀ →+* DeltaAdjoinDivision D d a := Ideal.Quotient.mk _
  have hpL : Function.Injective (fun x : L₀ => (p : L₀) * x) := by
    have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
    have h' : IsSMulRegular L₀ (p : L₀) := by simpa only [map_natCast] using h
    intro x z hxz
    apply h'
    simpa only [smul_eq_mul] using hxz
  have hC (r : A) :
      WittVector.map j (deltaWittGhostVector F₀ (MvPolynomial.C r)) =
        WittVector.map (deltaAdjoinDivisionMap D d a) (deltaWittGhostVector D r) := by
    ext n
    rw [WittVector.map_coeff, deltaWittGhostVector_relativeFree_C_coeff D hgL,
      WittVector.map_coeff]
    rfl
  have hz : WittVector.map j (deltaWittGhostVector F₀
      (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s))) = 0 := by
    ext n
    rw [WittVector.map_coeff, WittVector.zero_coeff]
    apply (deltaWittGhostVector_jets_zero_iff F₀ hpL hgL j
      (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s)) n).mp
      (fun i _ => deltaDivisionIteratedRelation_quotient_eq_zero D d a s i) n le_rfl
  change WittVector.map j (deltaWittGhostRingHom F₀ hgL
    (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s))) = 0 at hz
  rw [map_sub, map_mul, map_sub, map_mul] at hz
  change WittVector.map j (deltaWittGhostVector F₀ (MvPolynomial.C d)) *
    deltaDivisionRawWittPoint D d a s -
      WittVector.map j (deltaWittGhostVector F₀ (MvPolynomial.C (a s))) = 0 at hz
  rw [hC, hC] at hz
  exact sub_eq_zero.mp hz

include hpA in
/-- 概要：係数射と全 Witt 解を指定すると raw 包からの通常環射が一意に存在する。
方針：Witt 解による通常評価で存在を、Witt 点の外延性で一意性を示す。
規約：終域の δ 構造・p 正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の剰余比較に使う具体的普遍性。 -/
theorem existsUnique_deltaDivisionWittMap (d : A) (a : σ → A)
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hw : ∀ s, WittVector.map q (deltaWittGhostVector D d) * w s =
      WittVector.map q (deltaWittGhostVector D (a s))) :
    ∃! h : DeltaAdjoinDivision D d a →+* B,
      (∀ r, h (deltaAdjoinDivisionMap D d a r) = q r) ∧
        ∀ s, WittVector.map h (deltaDivisionRawWittPoint D d a s) = w s := by
  refine ⟨deltaDivisionWittMap D hpA q w d a hgL hw, ⟨?_, ?_⟩, ?_⟩
  · exact deltaDivisionWittMap_coeff D hpA q w d a hgL hw
  · exact deltaDivisionWittMap_point D hpA q w d a hgL hw
  · intro h hh
    apply deltaDivisionRingHom_ext_of_wittPoint D hpA d a
    · intro r
      rw [hh.1, deltaDivisionWittMap_coeff]
    · intro s
      rw [hh.2, deltaDivisionWittMap_point]

end SerrePositivity.BhattScholze.Andre
