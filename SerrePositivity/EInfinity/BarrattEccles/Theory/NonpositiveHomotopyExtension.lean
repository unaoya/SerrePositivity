module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.NonpositiveExtension

/-!
# 指定された非正次数のホモトピー同値を戻す

## 概要
HA 3.2.4.7 の等変な係数比較を、鎖複体から元の整数コチェイン複体へ戻す。

## 方針
鎖ホモトピーを延長し、制限と延長の自然同型で両端を元の複体へ戻す。

## 規約
元の射を制限して得た順射の場合、戻した順射を元の指定射そのものにする。

## 使われ方
テンソルと余不変を取る関手に適用する、実際の係数のホモトピー同値。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity
open CategoryTheory HomologicalComplex Limits
variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]

/-- 鎖複体の指定ホモトピー同値を q ↦ −q に沿って延長する。 -/
def extendDownNatHomotopyEquiv {P Q : ChainComplex C ℕ} (e : HomotopyEquiv P Q) :
    HomotopyEquiv (P.extend ComplexShape.embeddingDownNat)
      (Q.extend ComplexShape.embeddingDownNat) where
  hom := extendMap e.hom ComplexShape.embeddingDownNat
  inv := extendMap e.inv ComplexShape.embeddingDownNat
  homotopyHomInvId := by
    simpa only [extendMap_comp, extendMap_id] using
      e.homotopyHomInvId.extend ComplexShape.embeddingDownNat
  homotopyInvHomId := by
    simpa only [extendMap_comp, extendMap_id] using
      e.homotopyInvHomId.extend ComplexShape.embeddingDownNat

variable {K L : CochainComplex C ℤ}
  (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i))
  (hL : ∀ i : ℤ, 0 < i → IsZero (L.X i))
  (e : HomotopyEquiv (K.restriction ComplexShape.embeddingDownNat)
    (L.restriction ComplexShape.embeddingDownNat))

/-- 非正の複体の制限間の同値を、元の二つの複体へ戻す。 -/
def nonpositiveLiftHomotopyEquiv : HomotopyEquiv K L :=
  (HomotopyEquiv.ofIso (nonpositiveExtensionIso K hK).symm).trans
    ((extendDownNatHomotopyEquiv e).trans (HomotopyEquiv.ofIso (nonpositiveExtensionIso L hL)))

/-- 順射が元の指定射の制限なら、戻した順射もその指定射に一致する。 -/
lemma nonpositiveLiftHomotopyEquiv_hom (f : K ⟶ L)
    (he : e.hom = restrictionMap f ComplexShape.embeddingDownNat) :
    (nonpositiveLiftHomotopyEquiv hK hL e).hom = f := by
  change (nonpositiveExtensionIso K hK).inv ≫
    extendMap e.hom ComplexShape.embeddingDownNat ≫ (nonpositiveExtensionIso L hL).hom = f
  rw [he, nonpositiveExtensionIso_naturality K f hK hL, Iso.inv_hom_id_assoc]

/-- 指定順射をそのまま保持する、元の非正次数の複体間の同値。 -/
def nonpositiveLiftSpecifiedHomotopyEquiv (f : K ⟶ L)
    (he : e.hom = restrictionMap f ComplexShape.embeddingDownNat) : HomotopyEquiv K L :=
  (nonpositiveLiftHomotopyEquiv hK hL e).copy
    (Homotopy.ofEq (nonpositiveLiftHomotopyEquiv_hom hK hL e f he))

/-- 指定順射を保持して戻した同値の順射の式。 -/
@[simp]
lemma nonpositiveLiftSpecifiedHomotopyEquiv_hom (f : K ⟶ L)
    (he : e.hom = restrictionMap f ComplexShape.embeddingDownNat) :
    (nonpositiveLiftSpecifiedHomotopyEquiv hK hL e f he).hom = f := rfl

end SerrePositivity.EInfinity
