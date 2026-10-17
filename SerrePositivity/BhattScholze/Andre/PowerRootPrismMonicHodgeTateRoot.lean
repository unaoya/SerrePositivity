module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicHodgeTateBase

/-!
# André E1・E2：元の無限根入力の Hodge–Tate 候補における実根

## 概要

無限根変数 Y₀ の標準像は、元のモニック入力の prism 商への係数像の根となる。
BS Rem 7.15（著者版 p.62）の同じ実候補における根の計算。

## 方針

raw 包の dX=f(Y₀) を実完備化の分母商へ送り、分母像が零となることを使う。

## 規約

根の計算自体はモニック性・正次数・prism 商の p 正則性を要求しない。

## 使われ方

p 完全忠実平坦な具体的候補が元の多項式の根を持つことの確認。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "xP" => algebraMap A P (perfectPrismVarpiLift W hW)
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "dH" => uL (jL dP)
local notation "xH" => uL (jL xP)
local notation "T" => H ⧸ Ideal.span {dH}
local notation "qH" => Ideal.Quotient.mk (Ideal.span {dH})
local notation "R" => A ⧸ W.ideal
local notation "S" => H ⧸ Ideal.span {dH, xH}


/-- 概要：無限根変数 Y₀ の実完備化分母商への標準像。
方針：元の入力環から raw 包、実完備化、分母商へ順に送る。
規約：係数射と同じ標準射を使う。
使われ方：BS Rem 7.15（著者版 p.62）の根を持つ具体的候補。 -/
def powerRootPrismMonicHodgeTateRoot :
    let := pdCompletionCommRing L p (jL dP)
    T := by
  let := pdCompletionCommRing L p (jL dP)
  exact qH (uL (jL (powerRootPolynomialVariable A p hp 0)))

/-- 概要：指定した標準像は元の入力多項式の prism 商での係数像の根。
方針：raw 関係を分母商へ送り、係数射の一致と多項式評価の自然性を使う。
規約：根の計算にモニック性・正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の完全忠実平坦な根付き候補。 -/
theorem powerRootPrismMonicHodgeTateRoot_eval :
    let := pdCompletionCommRing L p (jL dP)
    (f.map (Ideal.Quotient.mk W.ideal)).eval₂ (powerRootPrismMonicHodgeTateBaseMap W hW f)
      (powerRootPrismMonicHodgeTateRoot W hW f) = 0 := by
  let := pdCompletionCommRing L p (jL dP)
  let k : P →+* T := (qH).comp ((uL).comp jL)
  have hd : k dP = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self dH)
  have hrel := congrArg (fun z : L => qH (uL z)) (deltaAdjoinDivision_relation E dP a default)
  simp only [map_mul, powerRootPrismMonicUnaryFamily, powerRootMonicPDInput] at hrel
  have hy : k (powerRootPolynomialBaseMap A p hp f) = 0 := by
    change k dP * qH (uL (deltaAdjoinDivisionVariable E dP a default)) =
      k (powerRootPolynomialBaseMap A p hp f) at hrel
    rw [hd, zero_mul] at hrel
    exact hrel.symm
  have hcoeff : (powerRootPrismMonicHodgeTateBaseMap W hW f).comp
      (Ideal.Quotient.mk W.ideal) = k.comp (algebraMap A P) := by
    ext r
    exact powerRootPrismMonicHodgeTateBaseMap_mk W hW f r
  rw [Polynomial.eval₂_map, hcoeff]
  change f.eval₂ (k.comp (algebraMap A P)) (k (powerRootPolynomialVariable A p hp 0)) = 0
  rw [← Polynomial.hom_eval₂]
  exact hy

end SerrePositivity.BhattScholze.Andre
