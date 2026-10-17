module
public import SerrePositivity.DifferentialGraded.Tensor.ComposeRightRestrictionActions
public import SerrePositivity.DifferentialGraded.Bimodule.ValueIsomorphism
public import SerrePositivity.DifferentialGraded.Module.Isomorphism

/-! # 外側右作用制限と相対tensor合成の全Hom自然な比較同型

## 概要
外側右作用制限と相対tensor合成の全Hom自然な比較同型。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D B)

/-- 値の比較を、外側右作用の全Homと可換な右加群同型へ束ねる。 -/
def composeRightRestrictionRightIso (P : Bimodule A B C) (Q : Bimodule A C E) (e : E) :
    ForgetEnrichment.of (Complex A)
        ((compose A D C E (Bimodule.rightRestriction A B D C F P) Q).rightAt e) ≅
      ForgetEnrichment.of (Complex A)
        ((Bimodule.rightRestriction A B D E F (compose A B C E P Q)).rightAt e) :=
  moduleIsoMk A D (fun d => composeRightRestrictionValueIso A B D C E F P Q d.unop e)
    (fun d d' => composeRightRestrictionValueIso_right_naturality A B D C E F P Q d d' e)

/-- 右作用制限と合成の比較は、残る左作用も全Homで保つ実際のbimodule同型。 -/
def composeRightRestrictionIso (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) :
    BimoduleCategory.of A D E
        (compose A D C E
          (Bimodule.rightRestriction A B D C F (BimoduleCategory.underlying A B C P))
          (BimoduleCategory.underlying A C E Q)) ≅
      (BimoduleCategory.middleRightRestrictionFunctor A B D E F).obj
        (BimoduleCategory.of A B E (compose A B C E
          (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q))) :=
  BimoduleCategory.isoOfValueFamily A D E
    (fun e => composeRightRestrictionRightIso A B D C E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) e) (by
    intro d e e'
    simp only [composeRightRestrictionRightIso, moduleIsoMk_hom_eval]
    exact composeRightRestrictionValueIso_left_naturality A B D C E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) d e e')

@[simp]
lemma composeRightRestrictionIso_hom_value (P : BimoduleCategory A B C)
    (Q : BimoduleCategory A C E) (d : D) (e : E) :
    (BimoduleCategory.valueEvaluation A D E d e).map
        (composeRightRestrictionIso A B D C E F P Q).hom =
      (composeRightRestrictionValueIso A B D C E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) d e).hom := by
  change (moduleEvaluation A D d).map
    (composeRightRestrictionRightIso A B D C E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) e).hom = _
  simp only [composeRightRestrictionRightIso, moduleIsoMk_hom_eval]

@[simp]
lemma composeRightRestrictionIso_inv_value (P : BimoduleCategory A B C)
    (Q : BimoduleCategory A C E) (d : D) (e : E) :
    (BimoduleCategory.valueEvaluation A D E d e).map
        (composeRightRestrictionIso A B D C E F P Q).inv =
      (composeRightRestrictionValueIso A B D C E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) d e).inv := by
  change (moduleEvaluation A D d).map
    (composeRightRestrictionRightIso A B D C E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) e).inv = _
  simp only [composeRightRestrictionRightIso, moduleIsoMk_inv_eval]

end SerrePositivity.DifferentialGraded.BimoduleTensor
