module
public import SerrePositivity.KST.SConstruction.ObjectKClassTriangle
public import SerrePositivity.KST.SConstruction.CofiberEvaluations

/-! # 元の cofiber 図式の対象 K 類の加法性
概要：任意の元の cofiber 正方形の中間項の K 類を両端の類の和として計算する。
方針：中央正方形を厳密に回収する S₂ 補完と、S₂ の三辺の加法関係を使う。
規約：零角や cofiber を新しく選び直さない。使われ方：三角圏 K₀ への普遍性の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- S₂ の長辺の評価は元の中央 cofiber 正方形の中間項を回収する。 -/
lemma sTwoFace_middle (X : StableModel.{u})
    (q : (objectSConstruction X.carrier) _⦋2⦌) :
    (sOneComparison X.carrier).app _ ((objectSConstruction X.carrier).δ 1 q) =
      (cofiberStableMiddle X).val.app _ ((sTwoCofiberRestriction X.carrier).app _ q) := by
  rfl

/-- S₂ の最初の短辺の評価は元の中央 cofiber 正方形の subobject を回収する。 -/
lemma sTwoFace_subobject (X : StableModel.{u})
    (q : (objectSConstruction X.carrier) _⦋2⦌) :
    (sOneComparison X.carrier).app _ ((objectSConstruction X.carrier).δ 2 q) =
      (cofiberStableSubobject X).val.app _ ((sTwoCofiberRestriction X.carrier).app _ q) := by
  rfl

/-- S₂ の最後の短辺の評価は元の中央 cofiber 正方形の quotient を回収する。 -/
lemma sTwoFace_quotient (X : StableModel.{u})
    (q : (objectSConstruction X.carrier) _⦋2⦌) :
    (sOneComparison X.carrier).app _ ((objectSConstruction X.carrier).δ 0 q) =
      (cofiberStableQuotient X).val.app _ ((sTwoCofiberRestriction X.carrier).app _ q) := by
  rfl

/-- 任意の元の cofiber 図式の実際の BF K 類は cofiber 加法関係を満たす。 -/
lemma objectKClass_cofiber (X : StableModel.{u})
    (v : (cofiberDiagrams X.carrier) _⦋0⦌) :
    objectKClass X ((cofiberStableMiddle X).val.app _ v) =
      objectKClass X ((cofiberStableSubobject X).val.app _ v) +
        objectKClass X ((cofiberStableQuotient X).val.app _ v) := by
  let q := (sTwoCofiberSection X.carrier).app (Opposite.op ⦋0⦌) v
  have h := objectKClass_sTwo X q
  have hp := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sTwoCofiberSection_projection X.carrier) (Opposite.op ⦋0⦌)) v
  change (sTwoCofiberRestriction X.carrier).app _ q = v at hp
  rw [sTwoFace_middle, sTwoFace_subobject, sTwoFace_quotient, hp] at h
  exact h

end SerrePositivity.KST.SConstruction
