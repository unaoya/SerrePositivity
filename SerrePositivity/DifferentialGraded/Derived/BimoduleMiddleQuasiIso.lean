module
public import SerrePositivity.DifferentialGraded.Tensor.FunctorRestrictionQuasiIso
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSourceFull

/-! # 準同値に沿う制限後モデルの実際のbimodule合成比較の準同型性

## 概要
準同値に沿う制限後モデルの実際のbimodule合成比較の準同型性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory Opposite MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)

/-- 直接の左制限を前合成の左加群表示へ替える、値での計算同型。 -/
def middleRestrictionResolvedValueIso (P : BimoduleCategory A B C)
    (R : BimoduleCategory A D E) (b : B) (e : E) :
    (compose A B D E (Bimodule.leftRestriction A B C D F
      (BimoduleCategory.underlying A B C P)) (BimoduleCategory.underlying A D E R)).value b e ≅
      BalancedTensor.obj A D ((BimoduleCategory.underlying A D E R).rightAt e)
        (F.comp ((BimoduleCategory.underlying A B C P).leftAt b)) :=
  BalancedTensor.changeLeft A D ((BimoduleCategory.underlying A D E R).rightAt e)
    (Bimodule.leftRestriction_leftAt A B C D F (BimoduleCategory.underlying A B C P) b)

omit [Small.{u} E] in
lemma middleRestrictionResolvedMap_value (P : BimoduleCategory A B C)
    (Q : BimoduleCategory A C E) (R : BimoduleCategory A D E)
    (q : R ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q)
    (b : B) (e : E) :
    (BimoduleCategory.valueEvaluation A B E b e).map
        (middleRestrictionResolvedMap A B C D E F P Q R q) =
      (middleRestrictionResolvedValueIso A B C D E F P R b e).hom ≫
        BalancedTensor.resolvedRestrictionComparison A D C F
          (R := (BimoduleCategory.evaluation A D E e).obj R)
          (M := (BimoduleCategory.evaluation A C E e).obj Q)
          (q.val e)
          ((BimoduleCategory.underlying A B C P).leftAt b) := by
  apply BalancedTensor.hom_ext A D ((BimoduleCategory.underlying A D E R).rightAt e)
    ((Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)).leftAt b)
  intro d
  simp only [middleRestrictionResolvedMap, CategoryTheory.Functor.map_comp,
    composeMap_value_eval, middleRestrictionComparisonMap_value_eval]
  have hm := ι_composeValueMap A B D E
    (𝟙 (BimoduleCategory.of A B D (Bimodule.leftRestriction A B C D F
      (BimoduleCategory.underlying A B C P)))) q b d e
  simp only [CategoryTheory.Functor.map_id] at hm
  have hl := congrArg (fun k => k ≫ middleRestrictionComparisonValue A B C D E F
    (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) b e) hm
  have hs := congrArg (fun k => ((BimoduleCategory.valueEvaluation A D E d e).map q ⊗ₘ
    𝟙 ((BimoduleCategory.underlying A B C P).value b (F.obj d))) ≫ k)
      (ι_middleRestrictionComparisonValue A B C D E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) b e d)
  have hleft := (Category.assoc _ _ _).symm.trans
    (hl.trans ((Category.assoc _ _ _).trans hs))
  have hc := BalancedTensor.ι_changeLeft_hom A D
    ((BimoduleCategory.underlying A D E R).rightAt e)
    (Bimodule.leftRestriction_leftAt A B C D F (BimoduleCategory.underlying A B C P) b) d
  have hc' := hc.trans (Category.id_comp _)
  have hr := congrArg (fun k => k ≫ BalancedTensor.resolvedRestrictionComparison A D C F
          (R := (BimoduleCategory.evaluation A D E e).obj R)
          (M := (BimoduleCategory.evaluation A C E e).obj Q)
    (q.val e)
    ((BimoduleCategory.underlying A B C P).leftAt b)) hc'
  have hres := BalancedTensor.ι_resolvedRestrictionComparison A D C F
    (R := (BimoduleCategory.evaluation A D E e).obj R)
    (M := (BimoduleCategory.evaluation A C E e).obj Q)
    (q.val e) ((BimoduleCategory.underlying A B C P).leftAt b) d
  have hright := (Category.assoc _ _ _).symm.trans (hr.trans hres)
  exact hleft.trans hright.symm

omit [Small.{u} E] in
/-- 任意の右K-flatな制限後モデルを使う実際のbimodule比較は準同型。 -/
lemma middleRestrictionResolvedMap_quasiIso (hF : QuasiEquivalence F)
    (P : BimoduleCategory A B C) (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) :
    BimoduleCategory.quasiIso A B E
      (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q) := by
  intro b e
  rw [middleRestrictionResolvedMap_value]
  have h := BalancedTensor.resolvedRestrictionComparison_quasiIso A D C F hF
    (R := (BimoduleCategory.evaluation A D E e).obj R.obj)
    (M := (BimoduleCategory.evaluation A C E e).obj Q.obj)
    (R.property e) (Q.property e) (q.val e)
    (fun d => hq d e) ((BimoduleCategory.underlying A B C P).leftAt b)
  let := h
  exact quasiIso_comp _ _

end SerrePositivity.DifferentialGraded.BimoduleTensor
