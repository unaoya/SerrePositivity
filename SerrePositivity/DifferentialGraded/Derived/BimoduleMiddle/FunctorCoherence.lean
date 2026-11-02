module

public import SerrePositivity.DifferentialGraded.Tensor.ResolvedRestriction
public import SerrePositivity.DifferentialGraded.Derived.Bimodule
public import SerrePositivity.DifferentialGraded.Bimodule.Value
public import SerrePositivity.DifferentialGraded.Bimodule.Right
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.IteratedModels

/-!
# Derived.BimoduleMiddle.FunctorCoherence

## 概要
中間圏制限の準同値、恒等・合成と反復比較の整合性をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## BimoduleMiddleQuasiIso（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleQuasiIso.lean） -/

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

@[expose] public section BimoduleMiddleQuasiIso
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end BimoduleMiddleQuasiIso

/-! ## BimoduleMiddleEquivalence（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleEquivalence.lean） -/

/-! # dg準同値に沿う中間圏比較の全導来自然同型

## 概要
dg準同値に沿う中間圏比較の全導来自然同型。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleEquivalence
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hF : QuasiEquivalence F) (hE : localHomKFlat A E)
include hF

lemma derivedMiddleRestrictionComparison_isIso (P : BimoduleCategory A B C)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) :
    IsIso (derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq) := by
  have hm := bimoduleToDerived_inverts A B E _
    (middleRestrictionResolvedMap_quasiIso A B C D E F hF P Q R q hq)
  let := hm
  unfold derivedMiddleRestrictionComparison
  infer_instance

lemma derivedMiddleRestrictionComparisonLocalized_isIso
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) :
    IsIso (derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q R q hq) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  obtain ⟨P, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (bimoduleToDerived A B C) X
  apply (NatTrans.isIso_app_iff_of_iso
    (derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q R q hq) e).mp
  rw [derivedMiddleRestrictionComparisonLocalized_app]
  have hi := derivedMiddleRestrictionComparison_isIso A B C D E F hF hE P Q R q hq
  let := hi
  infer_instance

lemma middleDerivedKFlatComparison_isIso :
    IsIso (middleDerivedKFlatComparison A B C D E F hE) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Q
  exact derivedMiddleRestrictionComparisonLocalized_isIso A B C D E F hF hE Q
    (rightKFlatResolutionObj A D E hE
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))
    (bimoduleCanonicalSemifreeResolution A D E _).π
    (bimoduleCanonicalSemifreeResolution A D E _).quasiIso

lemma middleRightKFlatLocalizedComparison_isIso :
    IsIso (middleRightKFlatLocalizedComparison A B C D E F hE) := by
  have hi := middleDerivedKFlatComparison_isIso A B C D E F hF hE
  let := hi
  exact (Localization.liftNatIso (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
    (middleDerivedSourceKFlatFunctor A B C D E F hE)
    (middleDerivedTargetKFlatFunctor A B C E hE)
    (middleRightKFlatLocalizedSource A B C D E F hE)
    (rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE)
    (asIso (middleDerivedKFlatComparison A B C D E F hE))).isIso_hom

lemma middleFullDerivedComparison_isIso :
    IsIso (middleFullDerivedComparison A B C D E F hE) := by
  have hi := middleRightKFlatLocalizedComparison_isIso A B C D E F hF hE
  let := hi
  unfold middleFullDerivedComparison
  infer_instance

lemma derivedMiddleRestrictionNatTrans_isIso :
    IsIso (derivedMiddleRestrictionNatTrans A B C D E F hE) := by
  have hi := middleFullDerivedComparison_isIso A B C D E F hF hE
  let := hi
  unfold derivedMiddleRestrictionNatTrans
  infer_instance

/-- 準同値に沿う中間圏の変更は、両変数の全導来射に自然な合成比較同型を与える。 -/
def derivedMiddleRestrictionIso :
    middleRestrictionDerivedSource A B C D E F hE ≅
      derivedBimoduleComposeFunctor A B C E hE := by
  have hi := derivedMiddleRestrictionNatTrans_isIso A B C D E F hF hE
  let := hi
  exact asIso (derivedMiddleRestrictionNatTrans A B C D E F hE)

lemma derivedMiddleRestrictionIso_hom :
    (derivedMiddleRestrictionIso A B C D E F hF hE).hom =
      derivedMiddleRestrictionNatTrans A B C D E F hE := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleEquivalence

/-! ## BimoduleMiddleResolvedCoherence（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleResolvedCoherence.lean） -/

/-! # 制限後モデルによるbimodule合成比較の自己・推移整合性

## 概要
制限後モデルによるbimodule合成比較の自己・推移整合性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleResolvedCoherence
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory Opposite MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] (F : DGFunctor A D E) (G : DGFunctor A E T)

omit [Small.{u} D] [Small.{u} E] [Small.{u} T] in
@[simp]
lemma middleLeftRestrictionCompObjIso_hom_value (P : BimoduleCategory A B T) (b : B) (d : D) :
    (BimoduleCategory.valueEvaluation A B D b d).map
        (BimoduleCategory.middleLeftRestrictionCompObjIso A B D E T F G P).hom = 𝟙 _ := by
  change (moduleEvaluation A B b).map ((BimoduleCategory.evaluation A B D d).map
    (BimoduleCategory.middleLeftRestrictionCompObjIso A B D E T F G P).hom) = 𝟙 _
  rw [BimoduleCategory.middleLeftRestrictionCompObjIso_hom_eval,
    CategoryTheory.Functor.map_id]

/-- 左制限の二段階表示を、後因子を保った合成のsource同型へ送る。 -/
def middleRestrictionCompSourceIso (P : BimoduleCategory A B T) (S : BimoduleCategory A D L) :
    (composeWith A B D L S).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)) ≅
      (composeWith A B D L S).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B T D (F.comp G)).obj P) :=
  (composeWith A B D L S).mapIso
    (BimoduleCategory.middleLeftRestrictionCompObjIso A B D E T F G P)

omit [Small.{u} E] [Small.{u} T] in
@[reassoc]
lemma ι_middleRestrictionCompSourceIso_hom_value
    (P : BimoduleCategory A B T) (S : BimoduleCategory A D L) (b : B) (l : L) (d : D) :
    BalancedTensor.ι A D ((BimoduleCategory.underlying A D L S).rightAt l)
        ((Bimodule.leftRestriction A B E D F (Bimodule.leftRestriction A B T E G
          (BimoduleCategory.underlying A B T P))).leftAt b) d ≫
        (BimoduleCategory.valueEvaluation A B L b l).map
          (middleRestrictionCompSourceIso A B D E T L F G P S).hom =
      BalancedTensor.ι A D ((BimoduleCategory.underlying A D L S).rightAt l)
        ((Bimodule.leftRestriction A B T D (F.comp G)
          (BimoduleCategory.underlying A B T P)).leftAt b) d := by
  have hm := ι_composeValueMap A B D L
    (BimoduleCategory.middleLeftRestrictionCompObjIso A B D E T F G P).hom (𝟙 S) b d l
  simp only [CategoryTheory.Functor.map_id, middleLeftRestrictionCompObjIso_hom_value,
    tensorHom_id, id_whiskerRight, Category.id_comp] at hm
  exact (congrArg (fun k => BalancedTensor.ι A D
    ((BimoduleCategory.underlying A D L S).rightAt l)
    ((Bimodule.leftRestriction A B E D F (Bimodule.leftRestriction A B T E G
      (BimoduleCategory.underlying A B T P))).leftAt b) d ≫ k)
    (composeMap_value_eval A B D L
      (BimoduleCategory.middleLeftRestrictionCompObjIso A B D E T F G P).hom (𝟙 S) b l)).trans hm

/-- 指定された制限後モデルからの比較を、coendの各包含で計算する。 -/
@[reassoc]
lemma ι_middleRestrictionResolvedMap_value
    (P : BimoduleCategory A B E) (Q : BimoduleCategory A E L) (R : BimoduleCategory A D L)
    (q : R ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj Q)
    (b : B) (l : L) (d : D) :
    BalancedTensor.ι A D ((BimoduleCategory.underlying A D L R).rightAt l)
        ((Bimodule.leftRestriction A B E D F (BimoduleCategory.underlying A B E P)).leftAt b) d ≫
        (BimoduleCategory.valueEvaluation A B L b l).map
          (middleRestrictionResolvedMap A B E D L F P Q R q) =
      ((BimoduleCategory.valueEvaluation A D L d l).map q ⊗ₘ
        𝟙 ((BimoduleCategory.underlying A B E P).value b (F.obj d))) ≫
          BalancedTensor.ι A E ((BimoduleCategory.underlying A E L Q).rightAt l)
            ((BimoduleCategory.underlying A B E P).leftAt b) (F.obj d) := by
  have hv := congrArg (fun k => BalancedTensor.ι A D
    ((BimoduleCategory.underlying A D L R).rightAt l)
    ((Bimodule.leftRestriction A B E D F (BimoduleCategory.underlying A B E P)).leftAt b) d ≫ k)
      (middleRestrictionResolvedMap_value A B E D L F P Q R q b l)
  have hc := (BalancedTensor.ι_changeLeft_hom A D
    ((BimoduleCategory.underlying A D L R).rightAt l)
    (Bimodule.leftRestriction_leftAt A B E D F (BimoduleCategory.underlying A B E P) b) d).trans
      (Category.id_comp _)
  have hr := congrArg (fun k => k ≫ BalancedTensor.resolvedRestrictionComparison A D E F
    (R := (BimoduleCategory.evaluation A D L l).obj R)
    (M := (BimoduleCategory.evaluation A E L l).obj Q)
    (q.val l) ((BimoduleCategory.underlying A B E P).leftAt b)) hc
  have hs := BalancedTensor.ι_resolvedRestrictionComparison A D E F
    (R := (BimoduleCategory.evaluation A D L l).obj R)
    (M := (BimoduleCategory.evaluation A E L l).obj Q)
    (q.val l) ((BimoduleCategory.underlying A B E P).leftAt b) d
  exact hv.trans ((Category.assoc _ _ _).symm.trans (hr.trans hs))

/-- 二段階の指定増大による実際のbimodule比較は、合成増大による比較と一致する。 -/
lemma middleRestrictionResolvedMap_functor_comp
    (P : BimoduleCategory A B T) (Q : BimoduleCategory A T L)
    (R : BimoduleCategory A E L) (S : BimoduleCategory A D L)
    (r : S ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R)
    (q : R ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q) :
    (middleRestrictionCompSourceIso A B D E T L F G P S).hom ≫
        middleRestrictionResolvedMap A B T D L (F.comp G) P Q S
          (BimoduleCategory.resolvedRestrictionAugmentationComp A D E T L F G r q) =
      middleRestrictionResolvedMap A B E D L F
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P) R S r ≫
        middleRestrictionResolvedMap A B T E L G P Q R q := by
  apply BimoduleCategory.value_hom_ext A B L
  intro b l
  simp only [CategoryTheory.Functor.map_comp]
  apply BalancedTensor.hom_ext A D ((BimoduleCategory.underlying A D L S).rightAt l)
    ((Bimodule.leftRestriction A B E D F (Bimodule.leftRestriction A B T E G
      (BimoduleCategory.underlying A B T P))).leftAt b)
  intro d
  let a := BimoduleCategory.resolvedRestrictionAugmentationComp A D E T L F G r q
  have hi := ι_middleRestrictionCompSourceIso_hom_value A B D E T L F G P S b l d
  have hc := ι_middleRestrictionResolvedMap_value A B D T L (F.comp G) P Q S a b l d
  simp only [a, BimoduleCategory.resolvedRestrictionAugmentationComp_value] at hc
  have hleft := (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (BimoduleCategory.valueEvaluation A B L b l).map
      (middleRestrictionResolvedMap A B T D L (F.comp G) P Q S a)) hi).trans hc)
  have h₁ := ι_middleRestrictionResolvedMap_value A B D E L F
    ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P) R S r b l d
  have h₂ := ι_middleRestrictionResolvedMap_value A B E T L G P Q R q b l (F.obj d)
  have hpre := congrArg (fun k => k ≫ (BimoduleCategory.valueEvaluation A B L b l).map
    (middleRestrictionResolvedMap A B T E L G P Q R q)) h₁
  have hpost := congrArg (fun k => ((BimoduleCategory.valueEvaluation A D L d l).map r ⊗ₘ
    𝟙 ((BimoduleCategory.underlying A B T P).value b (G.obj (F.obj d)))) ≫ k) h₂
  have hright := (Category.assoc _ _ _).symm.trans
    (hpre.trans ((Category.assoc _ _ _).trans hpost))
  let rd : (BimoduleCategory.underlying A D L S).value d l ⟶
      (BimoduleCategory.underlying A E L R).value (F.obj d) l :=
    (BimoduleCategory.valueEvaluation A D L d l).map r
  let qd : (BimoduleCategory.underlying A E L R).value (F.obj d) l ⟶
      (BimoduleCategory.underlying A T L Q).value (G.obj (F.obj d)) l :=
    (BimoduleCategory.valueEvaluation A E L (F.obj d) l).map q
  let V := (BimoduleCategory.underlying A B T P).value b (G.obj (F.obj d))
  have ht : ((rd ≫ qd) ⊗ₘ 𝟙 V) ≫ BalancedTensor.ι A T
      ((BimoduleCategory.underlying A T L Q).rightAt l)
      ((BimoduleCategory.underlying A B T P).leftAt b) (G.obj (F.obj d)) =
    (rd ⊗ₘ 𝟙 V) ≫ (qd ⊗ₘ 𝟙 V) ≫ BalancedTensor.ι A T
      ((BimoduleCategory.underlying A T L Q).rightAt l)
      ((BimoduleCategory.underlying A B T P).leftAt b) (G.obj (F.obj d)) := by
    rw [tensorHom_comp_tensorHom_assoc, Category.comp_id]
  exact hleft.trans (ht.trans hright.symm)

omit [Small.{u} D] in
@[simp]
lemma middleLeftRestrictionIdObjIso_hom_value (P : BimoduleCategory A B D) (b : B) (d : D) :
    (BimoduleCategory.valueEvaluation A B D b d).map
        (BimoduleCategory.middleLeftRestrictionIdObjIso A B D P).hom = 𝟙 _ := by
  change (moduleEvaluation A B b).map ((BimoduleCategory.evaluation A B D d).map
    (BimoduleCategory.middleLeftRestrictionIdObjIso A B D P).hom) = 𝟙 _
  rw [BimoduleCategory.middleLeftRestrictionIdObjIso_hom_eval,
    CategoryTheory.Functor.map_id]

/-- 恒等左制限の表示を、指定後因子との合成のsourceで元に戻す。 -/
def middleRestrictionIdSourceIso (P : BimoduleCategory A B D) (S : BimoduleCategory A D L) :
    (composeWith A B D L S).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P) ≅
      (composeWith A B D L S).obj P :=
  (composeWith A B D L S).mapIso (BimoduleCategory.middleLeftRestrictionIdObjIso A B D P)

@[reassoc]
lemma ι_middleRestrictionIdSourceIso_hom_value (P : BimoduleCategory A B D)
    (S : BimoduleCategory A D L) (b : B) (l : L) (d : D) :
    BalancedTensor.ι A D ((BimoduleCategory.underlying A D L S).rightAt l)
        ((Bimodule.leftRestriction A B D D (DGFunctor.id D)
          (BimoduleCategory.underlying A B D P)).leftAt b) d ≫
        (BimoduleCategory.valueEvaluation A B L b l).map
          (middleRestrictionIdSourceIso A B D L P S).hom =
      BalancedTensor.ι A D ((BimoduleCategory.underlying A D L S).rightAt l)
        ((BimoduleCategory.underlying A B D P).leftAt b) d := by
  have hm := ι_composeValueMap A B D L
    (BimoduleCategory.middleLeftRestrictionIdObjIso A B D P).hom (𝟙 S) b d l
  simp only [CategoryTheory.Functor.map_id, middleLeftRestrictionIdObjIso_hom_value,
    tensorHom_id, id_whiskerRight, Category.id_comp] at hm
  exact (congrArg (fun k => BalancedTensor.ι A D
    ((BimoduleCategory.underlying A D L S).rightAt l)
    ((Bimodule.leftRestriction A B D D (DGFunctor.id D)
      (BimoduleCategory.underlying A B D P)).leftAt b) d ≫ k)
    (composeMap_value_eval A B D L
      (BimoduleCategory.middleLeftRestrictionIdObjIso A B D P).hom (𝟙 S) b l)).trans hm

/-- 恒等dg関手の実際の比較は、左制限表示を戻し、正規化した増大と合成する射そのもの。 -/
lemma middleRestrictionResolvedMap_functor_id
    (P : BimoduleCategory A B D) (Q S : BimoduleCategory A D L)
    (q : S ⟶ (BimoduleCategory.middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q) :
    middleRestrictionResolvedMap A B D D L (DGFunctor.id D) P Q S q =
      (middleRestrictionIdSourceIso A B D L P S).hom ≫
        composeMap A B D L (𝟙 P) (BimoduleCategory.resolvedRestrictionAugmentationId A D L q) := by
  apply BimoduleCategory.value_hom_ext A B L
  intro b l
  simp only [CategoryTheory.Functor.map_comp]
  apply BalancedTensor.hom_ext A D ((BimoduleCategory.underlying A D L S).rightAt l)
    ((Bimodule.leftRestriction A B D D (DGFunctor.id D)
      (BimoduleCategory.underlying A B D P)).leftAt b)
  intro d
  have hc := ι_middleRestrictionResolvedMap_value A B D D L (DGFunctor.id D) P Q S q b l d
  have hs := ι_middleRestrictionIdSourceIso_hom_value A B D L P S b l d
  let a := BimoduleCategory.resolvedRestrictionAugmentationId A D L q
  have hm := ι_composeValueMap A B D L (𝟙 P) a b d l
  simp only [CategoryTheory.Functor.map_id, a,
    BimoduleCategory.resolvedRestrictionAugmentationId_value] at hm
  have ht := (congrArg (fun k => BalancedTensor.ι A D
    ((BimoduleCategory.underlying A D L S).rightAt l)
    ((BimoduleCategory.underlying A B D P).leftAt b) d ≫ k)
    (composeMap_value_eval A B D L (𝟙 P) a b l)).trans hm
  have hr := (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (BimoduleCategory.valueEvaluation A B L b l).map
      (composeMap A B D L (𝟙 P) a)) hs).trans ht)
  exact hc.trans hr.symm

/-- 恒等比較を、後因子の増大の後に左制限の表示を戻す順で計算する。 -/
lemma middleRestrictionResolvedMap_functor_id_exchange
    (P : BimoduleCategory A B D) (Q S : BimoduleCategory A D L)
    (q : S ⟶ (BimoduleCategory.middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q) :
    middleRestrictionResolvedMap A B D D L (DGFunctor.id D) P Q S q =
      composeMap A B D L
          (𝟙 ((BimoduleCategory.middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P))
          (BimoduleCategory.resolvedRestrictionAugmentationId A D L q) ≫
        composeMap A B D L (BimoduleCategory.middleLeftRestrictionIdObjIso A B D P).hom (𝟙 Q) := by
  rw [middleRestrictionResolvedMap_functor_id]
  change composeMap A B D L (BimoduleCategory.middleLeftRestrictionIdObjIso A B D P).hom
      (𝟙 S) ≫ composeMap A B D L (𝟙 P)
        (BimoduleCategory.resolvedRestrictionAugmentationId A D L q) = _
  rw [← composeMap_comp, ← composeMap_comp]
  simp only [Category.comp_id, Category.id_comp]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleResolvedCoherence

/-! ## BimoduleMiddleIdentity（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleIdentity.lean） -/

/-! # 恒等dg関手の実際の導来中間比較と制限の恒等自然同型の整合性

## 概要
恒等dg関手の実際の導来中間比較と制限の恒等自然同型の整合性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleIdentity
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (L : Type z) [DGCategory A L] [Small.{u} L] (hL : localHomKFlat A L)

/-- K-flat後因子での計算同型は、前因子の閉零射にも自然。 -/
lemma derivedBimoduleComposeKFlatValueIso_first_naturality
    (Q : RightKFlatBimoduleCategory A D L) {P P' : BimoduleCategory A B D} (f : P ⟶ P') :
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj Q.obj)).map
        ((bimoduleToDerived A B D).map f) ≫
      (derivedBimoduleComposeKFlatValueIso A B D L hL Q P').hom =
    (derivedBimoduleComposeKFlatValueIso A B D L hL Q P).hom ≫
      (bimoduleToDerived A B L).map (composeMap A B D L f (𝟙 Q.obj)) :=
  (derivedBimoduleComposeKFlatIso A B D L hL Q).hom.naturality
    ((bimoduleToDerived A B D).map f)

lemma derivedBimoduleComposeResolutionValueIso_self
    (Q : RightKFlatBimoduleCategory A D L) (P : BimoduleCategory A B D) :
    derivedBimoduleComposeResolutionValueIso A B D L hL Q.obj Q (𝟙 Q.obj)
        ((BimoduleCategory.quasiIso A D L).id_mem Q.obj) P =
      derivedBimoduleComposeKFlatValueIso A B D L hL Q P := by
  unfold derivedBimoduleComposeResolutionValueIso
  rw [derivedBimoduleComposeResolutionComputation_self]
  apply Iso.ext
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- 恒等の左右制限比較を既存の全導来合成へ送った、選択された解像度に依存しないsource同型。 -/
def derivedMiddleIdentitySourceIso (P : BimoduleCategory A B D)
    (Q : BimoduleCategory A D L) :
    ((derivedBimoduleComposeFunctor A B D L hL).obj
      ((bimoduleToDerived A D L).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q))).obj
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P)) ≅
      ((derivedBimoduleComposeFunctor A B D L hL).obj
        ((bimoduleToDerived A D L).obj Q)).obj ((bimoduleToDerived A B D).obj P) :=
  ((derivedBimoduleComposeFunctor A B D L hL).mapIso
      ((bimoduleToDerived A D L).mapIso
        (BimoduleCategory.middleRightRestrictionIdObjIso A D L Q))).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P)) ≪≫
    ((derivedBimoduleComposeFunctor A B D L hL).obj
      ((bimoduleToDerived A D L).obj Q)).mapIso
      ((bimoduleToDerived A B D).mapIso (BimoduleCategory.middleLeftRestrictionIdObjIso A B D P))

/-- 恒等dg関手の実際の導来比較は、左右の恒等制限比較から作るsource同型そのもの。 -/
lemma derivedMiddleRestrictionComparison_functor_id
    (P : BimoduleCategory A B D) (Q R : RightKFlatBimoduleCategory A D L)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj
      Q.obj) (hq : BimoduleCategory.quasiIso A D L q) :
    derivedMiddleRestrictionComparison A B D D L (DGFunctor.id D) hL P Q R q hq =
      (derivedMiddleIdentitySourceIso A B D L hL P Q.obj).hom := by
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P
  let a := BimoduleCategory.resolvedRestrictionAugmentationId A D L q
  let r : R ⟶ Q := ⟨a⟩
  let f := (BimoduleCategory.middleRightRestrictionIdObjIso A D L Q.obj).hom
  let g := (BimoduleCategory.middleLeftRestrictionIdObjIso A B D P).hom
  have hn := derivedBimoduleComposeResolutionValueIso_naturality A B D L hL R Q q
    (𝟙 Q.obj) hq ((BimoduleCategory.quasiIso A D L).id_mem Q.obj) f r (by
      change (bimoduleToDerived A D L).map q ≫ (bimoduleToDerived A D L).map f =
        (bimoduleToDerived A D L).map a ≫ (bimoduleToDerived A D L).map (𝟙 Q.obj)
      rw [CategoryTheory.Functor.map_id, Category.comp_id, ← CategoryTheory.Functor.map_comp]
      rfl) P₀
  rw [derivedBimoduleComposeResolutionValueIso_self] at hn
  change ((derivedBimoduleComposeFunctor A B D L hL).map
      ((bimoduleToDerived A D L).map f)).app ((bimoduleToDerived A B D).obj P₀) ≫
      (derivedBimoduleComposeKFlatValueIso A B D L hL Q P₀).hom =
    (middleRestrictionSourceComputation A B D D L (DGFunctor.id D) hL P Q.obj R q hq).hom ≫
      (bimoduleToDerived A B L).map (composeMap A B D L (𝟙 P₀) a) at hn
  have ht := derivedBimoduleComposeKFlatValueIso_first_naturality A B D L hL Q g
  have hr := congrArg (fun k => (bimoduleToDerived A B L).map k)
    (middleRestrictionResolvedMap_functor_id_exchange A B D L P Q.obj R.obj q)
  rw [CategoryTheory.Functor.map_comp] at hr
  apply (Iso.cancel_iso_hom_right _ _ (derivedBimoduleComposeKFlatValueIso A B D L hL Q P)).1
  unfold derivedMiddleRestrictionComparison
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (middleRestrictionSourceComputation A B D D L (DGFunctor.id D) hL P Q.obj R q hq).hom ≫
      (bimoduleToDerived A B L).map
        (middleRestrictionResolvedMap A B D D L (DGFunctor.id D) P Q.obj R.obj q) =
    (((derivedBimoduleComposeFunctor A B D L hL).map
      ((bimoduleToDerived A D L).map f)).app ((bimoduleToDerived A B D).obj P₀) ≫
      ((derivedBimoduleComposeFunctor A B D L hL).obj
        ((bimoduleToDerived A D L).obj Q.obj)).map ((bimoduleToDerived A B D).map g)) ≫
      (derivedBimoduleComposeKFlatValueIso A B D L hL Q P).hom
  rw [hr, ← Category.assoc, ← hn, Category.assoc, ← ht, ← Category.assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleIdentity

/-! ## BimoduleMiddleFunctorComposition（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleFunctorComposition.lean） -/

/-! # dg関手の合成と指定モデルによる実際の導来中間比較の整合性

## 概要
dg関手の合成と指定モデルによる実際の導来中間比較の整合性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleFunctorComposition
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (L : Type s) [DGCategory A L] [Small.{u} L] (hL : localHomKFlat A L)

lemma derivedBimoduleComposeResolutionValueIso_first_naturality
    (Q : BimoduleCategory A D L) (R : RightKFlatBimoduleCategory A D L)
    (q : R.obj ⟶ Q) (hq : BimoduleCategory.quasiIso A D L q)
    {P P' : BimoduleCategory A B D} (f : P ⟶ P') :
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj Q)).map
        ((bimoduleToDerived A B D).map f) ≫
      (derivedBimoduleComposeResolutionValueIso A B D L hL Q R q hq P').hom =
    (derivedBimoduleComposeResolutionValueIso A B D L hL Q R q hq P).hom ≫
      (bimoduleToDerived A B L).map (composeMap A B D L f (𝟙 R.obj)) := by
  change _ ≫ (_ ≫ 𝟙 _) = (_ ≫ 𝟙 _) ≫ _
  simp only [Category.comp_id]
  exact (derivedBimoduleComposeResolutionComputation A B D L hL Q R q hq).hom.naturality
    ((bimoduleToDerived A B D).map f)

lemma derivedBimoduleComposeResolutionValueIso_fac
    (Q : BimoduleCategory A D L) (R : RightKFlatBimoduleCategory A D L)
    (q : R.obj ⟶ Q) (hq : BimoduleCategory.quasiIso A D L q) (P : BimoduleCategory A B D) :
    ((derivedBimoduleComposeFunctor A B D L hL).map ((bimoduleToDerived A D L).map q)).app
        ((bimoduleToDerived A B D).obj P) ≫
      (derivedBimoduleComposeResolutionValueIso A B D L hL Q R q hq P).hom =
    (derivedBimoduleComposeKFlatValueIso A B D L hL R P).hom := by
  have h := NatTrans.congr_app
    (derivedBimoduleComposeResolutionComputation_fac A B D L hL Q R q hq)
    ((bimoduleToDerived A B D).obj P)
  change _ ≫ (_ ≫ 𝟙 _) = _
  rw [Category.comp_id]
  exact h

variable (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 二段階比較のsourceを、合成関手による比較のsourceへ結ぶ自然な計算同型。 -/
def derivedMiddleCompositeSourceIso
    (P : BimoduleCategory A B T) (Q : BimoduleCategory A T L) (R : BimoduleCategory A E L)
    (q : R ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q)
    (hq : BimoduleCategory.quasiIso A E L q) :
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj
      ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R))).obj
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))) ≅
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj
      ((BimoduleCategory.middleRightRestrictionFunctor A T D L (F.comp G)).obj Q))).obj
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B T D (F.comp G)).obj P)) :=
  ((derivedBimoduleComposeFunctor A B D L hL).mapIso
    (bimoduleDerivedIso A D L (BimoduleCategory.middleRightRestrictionCompositeMap A D E T L F G q)
      (BimoduleCategory.middleRightRestrictionCompositeMap_quasiIso A D E T L F G q hq))).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))) ≪≫
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj
      ((BimoduleCategory.middleRightRestrictionFunctor A T D L (F.comp G)).obj Q))).mapIso
      ((bimoduleToDerived A B D).mapIso
        (BimoduleCategory.middleLeftRestrictionCompObjIso A B D E T F G P))

/-- 合成比較のsource同型は、同じ最終モデルによる導来合成の計算と可換。 -/
lemma derivedMiddleCompositeSourceIso_computation
    (P : BimoduleCategory A B T) (Q : RightKFlatBimoduleCategory A T L)
    (R : RightKFlatBimoduleCategory A E L) (S : RightKFlatBimoduleCategory A D L)
    (r : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R.obj)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q.obj)
    (hr : BimoduleCategory.quasiIso A D L r) (hq : BimoduleCategory.quasiIso A E L q) :
    (derivedMiddleCompositeSourceIso A B D L hL E T F G P Q.obj R.obj q hq).hom ≫
        (middleRestrictionSourceComputation A B T D L (F.comp G) hL P Q.obj S
          (BimoduleCategory.resolvedRestrictionAugmentationComp A D E T L F G r q)
          (BimoduleCategory.resolvedRestrictionAugmentationComp_quasiIso
            A D E T L F G r q hr hq)).hom =
      (middleRestrictionSourceComputation A B E D L F hL
        ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P) R.obj S r hr).hom ≫
        (bimoduleToDerived A B L).map
          (middleRestrictionCompSourceIso A B D E T L F G P S.obj).hom := by
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P
  let P₂ := (BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj P₀
  let k := BimoduleCategory.middleRightRestrictionCompositeMap A D E T L F G q
  let a := BimoduleCategory.resolvedRestrictionAugmentationComp A D E T L F G r q
  have ha := BimoduleCategory.resolvedRestrictionAugmentationComp_quasiIso
    A D E T L F G r q hr hq
  have h₀ := derivedBimoduleComposeResolutionValueIso_naturality A B D L hL S S r a hr ha
    k (𝟙 S) (by
      change (bimoduleToDerived A D L).map r ≫ (bimoduleToDerived A D L).map k =
        (bimoduleToDerived A D L).map (𝟙 S.obj) ≫ (bimoduleToDerived A D L).map a
      rw [CategoryTheory.Functor.map_id, Category.id_comp, ← CategoryTheory.Functor.map_comp]
      rfl) P₂
  change _ = (derivedBimoduleComposeResolutionValueIso A B D L hL
    ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R.obj) S r hr P₂).hom ≫
      (bimoduleToDerived A B L).map (composeMap A B D L (𝟙 P₂) (𝟙 S.obj)) at h₀
  let c := derivedBimoduleComposeResolutionValueIso A B D L hL
    ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R.obj) S r hr P₂
  have hpost := congrArg (fun f => c.hom ≫ (bimoduleToDerived A B L).map f)
    (composeMap_id A B D L P₂ S.obj)
  have hlast := (congrArg (fun f => c.hom ≫ f)
    ((bimoduleToDerived A B L).map_id ((composeWith A B D L S.obj).obj P₂))).trans
      (Category.comp_id _)
  replace h₀ := h₀.trans (hpost.trans hlast)
  change ((derivedBimoduleComposeFunctor A B D L hL).map
      ((bimoduleToDerived A D L).map k)).app ((bimoduleToDerived A B D).obj P₂) ≫
      (derivedBimoduleComposeResolutionValueIso A B D L hL
        ((BimoduleCategory.middleRightRestrictionFunctor A T D L (F.comp G)).obj Q.obj)
        S a ha P₂).hom =
    (middleRestrictionSourceComputation A B E D L F hL P₀ R.obj S r hr).hom at h₀
  have h₁ := derivedBimoduleComposeResolutionValueIso_first_naturality A B D L hL
    ((BimoduleCategory.middleRightRestrictionFunctor A T D L (F.comp G)).obj Q.obj) S a ha
    (BimoduleCategory.middleLeftRestrictionCompObjIso A B D E T F G P).hom
  change (((derivedBimoduleComposeFunctor A B D L hL).map
      ((bimoduleToDerived A D L).map k)).app ((bimoduleToDerived A B D).obj P₂) ≫
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj
      ((BimoduleCategory.middleRightRestrictionFunctor A T D L (F.comp G)).obj Q.obj))).map
      ((bimoduleToDerived A B D).map
        (BimoduleCategory.middleLeftRestrictionCompObjIso A B D E T F G P).hom)) ≫
      (middleRestrictionSourceComputation A B T D L (F.comp G) hL P Q.obj S a ha).hom = _
  have hs := congrArg (fun f => ((derivedBimoduleComposeFunctor A B D L hL).map
    ((bimoduleToDerived A D L).map k)).app ((bimoduleToDerived A B D).obj P₂) ≫ f) h₁
  have ht := congrArg (fun f => f ≫ (bimoduleToDerived A B L).map
    (middleRestrictionCompSourceIso A B D E T L F G P S.obj).hom) h₀
  exact (Category.assoc _ _ _).trans
    (hs.trans ((Category.assoc _ _ _).symm.trans ht))

/-- 二つのdg関手と指定右K-flatモデルによる実際の導来比較は、合成関手の比較と可換。 -/
lemma derivedMiddleRestrictionComparison_functor_comp
    (P : BimoduleCategory A B T) (Q : RightKFlatBimoduleCategory A T L)
    (R : RightKFlatBimoduleCategory A E L) (S : RightKFlatBimoduleCategory A D L)
    (r : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R.obj)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q.obj)
    (hr : BimoduleCategory.quasiIso A D L r) (hq : BimoduleCategory.quasiIso A E L q) :
    (derivedMiddleCompositeSourceIso A B D L hL E T F G P Q.obj R.obj q hq).hom ≫
        derivedMiddleRestrictionComparison A B T D L (F.comp G) hL P Q S
          (BimoduleCategory.resolvedRestrictionAugmentationComp A D E T L F G r q)
          (BimoduleCategory.resolvedRestrictionAugmentationComp_quasiIso
            A D E T L F G r q hr hq) =
      derivedMiddleRestrictionComparison A B E D L F hL
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P) R S r hr ≫
        ((derivedBimoduleComposeFunctor A B E L hL).map ((bimoduleToDerived A E L).map q)).app
          ((bimoduleToDerived A B E).obj
            ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)) ≫
        derivedMiddleRestrictionComparison A B T E L G hL P Q R q hq := by
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P
  let a := BimoduleCategory.resolvedRestrictionAugmentationComp A D E T L F G r q
  have ha := BimoduleCategory.resolvedRestrictionAugmentationComp_quasiIso
    A D E T L F G r q hr hq
  let c₀ := middleRestrictionSourceComputation A B E D L F hL P₀ R.obj S r hr
  let c₁ := middleRestrictionSourceComputation A B T E L G hL P Q.obj R q hq
  let c₂ := middleRestrictionSourceComputation A B T D L (F.comp G) hL P Q.obj S a ha
  let i := derivedMiddleCompositeSourceIso A B D L hL E T F G P Q.obj R.obj q hq
  let τ := derivedBimoduleComposeKFlatValueIso A B E L hL R P₀
  let v := ((derivedBimoduleComposeFunctor A B E L hL).map
    ((bimoduleToDerived A E L).map q)).app ((bimoduleToDerived A B E).obj P₀)
  let f := (bimoduleToDerived A B L).map
    (middleRestrictionResolvedMap A B E D L F P₀ R.obj S.obj r)
  let g := (bimoduleToDerived A B L).map
    (middleRestrictionResolvedMap A B T E L G P Q.obj R.obj q)
  let t := (bimoduleToDerived A B L).map
    (middleRestrictionResolvedMap A B T D L (F.comp G) P Q.obj S.obj a)
  let j := (bimoduleToDerived A B L).map
    (middleRestrictionCompSourceIso A B D E T L F G P S.obj).hom
  have hi : i.hom ≫ c₂.hom = c₀.hom ≫ j :=
    derivedMiddleCompositeSourceIso_computation A B D L hL E T F G P Q R S r q hr hq
  have hv : v ≫ c₁.hom = τ.hom :=
    derivedBimoduleComposeResolutionValueIso_fac A B E L hL _ R q hq P₀
  have hj : j ≫ t = f ≫ g := by
    have h := congrArg (fun k => (bimoduleToDerived A B L).map k)
      (middleRestrictionResolvedMap_functor_comp A B D E T L F G P Q.obj R.obj S.obj r q)
    simpa only [CategoryTheory.Functor.map_comp] using h
  apply (Iso.cancel_iso_hom_right _ _ (derivedBimoduleComposeKFlatValueIso A B T L hL Q P)).1
  unfold derivedMiddleRestrictionComparison
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change i.hom ≫ c₂.hom ≫ t = c₀.hom ≫ f ≫ τ.inv ≫ v ≫ c₁.hom ≫ g
  rw [← Category.assoc i.hom c₂.hom t, hi, Category.assoc, hj,
    ← Category.assoc v c₁.hom g, hv, Iso.inv_hom_id_assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleFunctorComposition

/-! ## BimoduleMiddleCanonicalComposition（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleCanonicalComposition.lean） -/

/-! # 標準semifree解像度による導来中間比較のdg関手合成則

## 概要
標準semifree解像度による導来中間比較のdg関手合成則。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleCanonicalComposition
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

/-- 二段階の標準解像度による比較は、合成関手へ直接適用する標準比較と可換。 -/
lemma derivedMiddleRestrictionCanonicalComparison_functor_comp
    (P : BimoduleCategory A B T) (Q : RightKFlatBimoduleCategory A T L) :
    let R := bimoduleCanonicalSemifreeResolution A E L
      ((BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q.obj)
    (derivedMiddleCompositeSourceIso A B D L hL E T F G P Q.obj R.obj R.π R.quasiIso).hom ≫
        derivedMiddleRestrictionCanonicalComparison A B T D L (F.comp G) hL P Q =
      derivedMiddleRestrictionCanonicalComparison A B E D L F hL
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)
          (R.toRightKFlat A E L hL) ≫
        ((derivedBimoduleComposeFunctor A B E L hL).map ((bimoduleToDerived A E L).map R.π)).app
          ((bimoduleToDerived A B E).obj
            ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)) ≫
        derivedMiddleRestrictionCanonicalComparison A B T E L G hL P Q := by
  let R := bimoduleCanonicalSemifreeResolution A E L
    ((BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q.obj)
  let S := bimoduleCanonicalSemifreeResolution A D L
    ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R.obj)
  let k := BimoduleCategory.middleRightRestrictionCompositeMap A D E T L F G R.π
  have hk := BimoduleCategory.middleRightRestrictionCompositeMap_quasiIso
    A D E T L F G R.π R.quasiIso
  let S' := S.postcompose A D L k hk
  have hi := derivedMiddleRestrictionComparison_semifree_eq_canonical A B T D L
    (F.comp G) hL Q S' P
  change derivedMiddleRestrictionComparison A B T D L (F.comp G) hL P Q
      (S.toRightKFlat A D L hL)
      (BimoduleCategory.resolvedRestrictionAugmentationComp A D E T L F G S.π R.π)
      (BimoduleCategory.resolvedRestrictionAugmentationComp_quasiIso
        A D E T L F G S.π R.π S.quasiIso R.quasiIso) =
    derivedMiddleRestrictionCanonicalComparison A B T D L (F.comp G) hL P Q at hi
  have h := derivedMiddleRestrictionComparison_functor_comp A B D L hL E T F G P Q
    (R.toRightKFlat A E L hL) (S.toRightKFlat A D L hL) S.π R.π S.quasiIso R.quasiIso
  rw [hi] at h
  exact h

/-- 標準解像度による恒等比較も、解像度を含まない左右の恒等制限比較に一致する。 -/
lemma derivedMiddleRestrictionCanonicalComparison_functor_id
    (P : BimoduleCategory A B D) (Q : RightKFlatBimoduleCategory A D L) :
    derivedMiddleRestrictionCanonicalComparison A B D D L (DGFunctor.id D) hL P Q =
      (derivedMiddleIdentitySourceIso A B D L hL P Q.obj).hom :=
  derivedMiddleRestrictionComparison_functor_id A B D L hL P Q
    (rightKFlatResolutionObj A D L hL
      ((BimoduleCategory.middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q.obj))
    (bimoduleCanonicalSemifreeResolution A D L _).π
    (bimoduleCanonicalSemifreeResolution A D L _).quasiIso

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleCanonicalComposition

/-! ## BimoduleMiddleIdentityFamily（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleIdentityFamily.lean） -/

/-! # 恒等中間比較の解像度を含まないsource同型を関手族へ束ねる

## 概要
恒等中間比較の解像度を含まないsource同型を関手族へ束ねる。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleIdentityFamily
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (L : Type z) [DGCategory A L] [Small.{u} L] (hL : localHomKFlat A L)

/-- 左右の恒等制限の自然同型だけから構成する、閉零両因子上のsource正規化同型。 -/
def middleClosedIdentityIso :
    middleClosedSourceFunctor A B D D L (DGFunctor.id D) hL ≅
      bimoduleToDerived A D L ⋙ derivedBimoduleComposeFunctor A B D L hL ⋙
        (whiskeringLeft _ _ _).obj (bimoduleToDerived A B D) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (BimoduleCategory.middleRightRestrictionIdIso A D L)
        (bimoduleToDerived A D L) ≪≫ Functor.leftUnitor _)
      (derivedBimoduleComposeFunctor A B D L hL ⋙
        (whiskeringLeft _ _ _).obj
          (BimoduleCategory.middleLeftRestrictionFunctor A B D D (DGFunctor.id D) ⋙
            bimoduleToDerived A B D)) ≪≫
    Functor.isoWhiskerLeft (bimoduleToDerived A D L ⋙ derivedBimoduleComposeFunctor A B D L hL)
      ((whiskeringLeft _ _ _).mapIso
        (Functor.isoWhiskerRight (BimoduleCategory.middleLeftRestrictionIdIso A B D)
          (bimoduleToDerived A B D) ≪≫ Functor.leftUnitor _))

lemma middleClosedIdentityIso_hom_app (Q : BimoduleCategory A D L)
    (P : BimoduleCategory A B D) :
    ((middleClosedIdentityIso A B D L hL).hom.app Q).app P =
      (derivedMiddleIdentitySourceIso A B D L hL P Q).hom := by
  change (((derivedBimoduleComposeFunctor A B D L hL).map
    ((bimoduleToDerived A D L).map
      (BimoduleCategory.middleRightRestrictionIdObjIso A D L Q).hom ≫ 𝟙 _)).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P)) ≫
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj Q)).map
      ((bimoduleToDerived A B D).map
        (BimoduleCategory.middleLeftRestrictionIdObjIso A B D P).hom ≫ 𝟙 _)) = _
  rw [Category.comp_id, Category.comp_id]
  rfl

/-- 指定右K-flat後因子について、恒等比較のsourceを閉零前因子の関手上で正規化する。 -/
def middleIdentitySourceFamilyIso (Q : RightKFlatBimoduleCategory A D L) :
    middleDerivedSourceFamily A B D D L (DGFunctor.id D) hL Q ≅
      middleDerivedTargetFamily A B D L hL Q :=
  (middleClosedIdentityIso A B D L hL).app Q.obj

lemma derivedMiddleRestrictionCanonicalFamily_functor_id (Q : RightKFlatBimoduleCategory A D L) :
    derivedMiddleRestrictionCanonicalFamily A B D D L (DGFunctor.id D) hL Q =
      (middleIdentitySourceFamilyIso A B D L hL Q).hom := by
  apply NatTrans.ext
  funext P
  rw [derivedMiddleRestrictionCanonicalFamily_app,
    derivedMiddleRestrictionCanonicalComparison_functor_id]
  exact (middleClosedIdentityIso_hom_app A B D L hL Q.obj P).symm

/-- 前因子の全導来圏へ、左右の恒等制限のsource正規化同型を降ろす。 -/
def middleIdentitySourceLiftIso (Q : RightKFlatBimoduleCategory A D L) :
    middleDerivedSourceLift A B D D L (DGFunctor.id D) hL Q ≅
      (derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj Q.obj) :=
  Localization.liftNatIso (bimoduleToDerived A B D) (BimoduleCategory.quasiIso A B D)
    (middleDerivedSourceFamily A B D D L (DGFunctor.id D) hL Q)
    (middleDerivedTargetFamily A B D L hL Q)
    (middleDerivedSourceLift A B D D L (DGFunctor.id D) hL Q)
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj Q.obj))
    (middleIdentitySourceFamilyIso A B D L hL Q)

lemma derivedMiddleRestrictionCanonicalLocalized_functor_id
    (Q : RightKFlatBimoduleCategory A D L) :
    derivedMiddleRestrictionCanonicalLocalized A B D D L (DGFunctor.id D) hL Q =
      (middleIdentitySourceLiftIso A B D L hL Q).hom := by
  rw [← derivedMiddleRestrictionCanonicalFamily_lift,
    derivedMiddleRestrictionCanonicalFamily_functor_id]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleIdentityFamily

/-! ## BimoduleMiddleIdentityFull（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleIdentityFull.lean） -/

/-! # 恒等中間比較と左右制限のsource正規化の全導来関手族上での一致

## 概要
恒等中間比較と左右制限のsource正規化の全導来関手族上での一致。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleIdentityFull
universe u v w z

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (L : Type z) [DGCategory A L] [Small.{u} L] (hL : localHomKFlat A L)

/-- 左右の恒等制限から作る正規化同型は、右K-flat後因子の任意の閉零射にも自然。 -/
def middleIdentityKFlatIso :
    middleDerivedSourceKFlatFunctor A B D D L (DGFunctor.id D) hL ≅
      middleDerivedTargetKFlatFunctor A B D L hL :=
  NatIso.ofComponents (middleIdentitySourceLiftIso A B D L hL) (by
    intro Q Q' g
    change middleDerivedSourceLiftMap A B D D L (DGFunctor.id D) hL g ≫
        (middleIdentitySourceLiftIso A B D L hL Q').hom =
      (middleIdentitySourceLiftIso A B D L hL Q).hom ≫
        (derivedBimoduleComposeFunctor A B D L hL).map ((bimoduleToDerived A D L).map g.hom)
    rw [← derivedMiddleRestrictionCanonicalLocalized_functor_id A B D L hL Q',
      ← derivedMiddleRestrictionCanonicalLocalized_functor_id A B D L hL Q]
    exact derivedMiddleRestrictionCanonicalLocalized_second_naturality
      A B D D L (DGFunctor.id D) hL g)

lemma middleDerivedKFlatComparison_functor_id :
    middleDerivedKFlatComparison A B D D L (DGFunctor.id D) hL =
      (middleIdentityKFlatIso A B D L hL).hom := by
  apply NatTrans.ext
  funext Q
  exact derivedMiddleRestrictionCanonicalLocalized_functor_id A B D L hL Q

/-- 指定右K-flat局所化上のsource正規化同型。 -/
def middleIdentityLocalizedIso :
    middleRightKFlatLocalizedSource A B D D L (DGFunctor.id D) hL ≅
      rightKFlatDerivedInclusion A D L ⋙ derivedBimoduleComposeFunctor A B D L hL :=
  Localization.liftNatIso (rightKFlatToDerived A D L) (rightKFlatQuasiIso A D L)
    (middleDerivedSourceKFlatFunctor A B D D L (DGFunctor.id D) hL)
    (middleDerivedTargetKFlatFunctor A B D L hL)
    (middleRightKFlatLocalizedSource A B D D L (DGFunctor.id D) hL)
    (rightKFlatDerivedInclusion A D L ⋙ derivedBimoduleComposeFunctor A B D L hL)
    (middleIdentityKFlatIso A B D L hL)

lemma middleRightKFlatLocalizedComparison_functor_id :
    middleRightKFlatLocalizedComparison A B D D L (DGFunctor.id D) hL =
      (middleIdentityLocalizedIso A B D L hL).hom := by
  unfold middleRightKFlatLocalizedComparison middleIdentityLocalizedIso
  rw [middleDerivedKFlatComparison_functor_id]
  rfl

/-- 両変数の全導来圏上のsource正規化。実際の比較射の可逆性から定義していない。 -/
def middleFullIdentityIso :
    middleFullDerivedSource A B D D L (DGFunctor.id D) hL ≅
      derivedBimoduleComposeFunctor A B D L hL :=
  Functor.isoWhiskerLeft (derivedRightKFlatReplacement A D L hL)
    (middleIdentityLocalizedIso A B D L hL) ≪≫ middleFullDerivedTargetIso A B D L hL

lemma middleFullDerivedComparison_functor_id :
    middleFullDerivedComparison A B D D L (DGFunctor.id D) hL =
      (middleFullIdentityIso A B D L hL).hom := by
  unfold middleFullDerivedComparison middleFullIdentityIso
  rw [middleRightKFlatLocalizedComparison_functor_id]
  rfl

/-- 既存の導来制限・導来合成で表したsourceを正規化する、両変数の全導来自然同型。 -/
def derivedMiddleIdentityIso :
    middleRestrictionDerivedSource A B D D L (DGFunctor.id D) hL ≅
      derivedBimoduleComposeFunctor A B D L hL :=
  (middleFullDerivedSourceIdentification A B D D L (DGFunctor.id D) hL).symm ≪≫
    middleFullIdentityIso A B D L hL

/-- 既存の実際の全導来比較は、左右制限の恒等同型から構成した正規化に一致する。 -/
lemma derivedMiddleRestrictionNatTrans_functor_id :
    derivedMiddleRestrictionNatTrans A B D D L (DGFunctor.id D) hL =
      (derivedMiddleIdentityIso A B D L hL).hom := by
  unfold derivedMiddleRestrictionNatTrans derivedMiddleIdentityIso
  rw [middleFullDerivedComparison_functor_id]
  rfl

lemma derivedMiddleIdentityIso_transport :
    (middleFullDerivedSourceIdentification A B D D L (DGFunctor.id D) hL).hom ≫
        (derivedMiddleIdentityIso A B D L hL).hom = (middleFullIdentityIso A B D L hL).hom := by
  unfold derivedMiddleIdentityIso
  rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleIdentityFull

/-! ## BimoduleMiddleAugmentedSource（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleAugmentedSource.lean） -/

/-! # 制限後の指定モデルから二段階の全導来sourceへの増大

## 概要
制限後の指定モデルから二段階の全導来sourceへの増大。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleAugmentedSource
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

/-- 増大をさらにFで制限し、閉零表示同型を通じて全導来sourceへ送る。 -/
def middleIteratedAugmentedSourceMap
    (Q : BimoduleCategory A T L) (P : BimoduleCategory A B T)
    (R : BimoduleCategory A E L)
    (q : R ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q) :
    ((derivedBimoduleComposeFunctor A B D L hL).obj
      ((bimoduleToDerived A D L).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R))).obj
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))) ⟶
    ((middleIteratedDerivedSource A B D E T L F G hL).obj
      ((bimoduleToDerived A T L).obj Q)).obj ((bimoduleToDerived A B T).obj P) :=
  ((derivedBimoduleComposeFunctor A B D L hL).map
      ((bimoduleToDerived A D L).map
        ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).map q))).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))) ≫
    (middleIteratedClosedSourceIso A B D E T L F G hL Q P).hom

/-- 全導来sourceの正規化は、指定モデルに対する既存の合成source同型と可換。 -/
lemma middleIteratedAugmentedSourceMap_normalize
    (Q : BimoduleCategory A T L) (P : BimoduleCategory A B T)
    (R : BimoduleCategory A E L)
    (q : R ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q)
    (hq : BimoduleCategory.quasiIso A E L q) :
    middleIteratedAugmentedSourceMap A B D E T L F G hL Q P R q ≫
        ((middleIteratedDerivedSourceIso A B D E T L F G hL).hom.app
          ((bimoduleToDerived A T L).obj Q)).app ((bimoduleToDerived A B T).obj P) =
      (derivedMiddleCompositeSourceIso A B D L hL E T F G P Q R q hq).hom ≫
        ((middleClosedSourceIdentification A B T D L (F.comp G) hL).hom.app Q).app P := by
  unfold middleIteratedAugmentedSourceMap
  rw [Category.assoc, middleIteratedClosedSourceIso_normalize]
  simp only [derivedMiddleCompositeSourceIso, middleIteratedClosedNormalizationIso,
    BimoduleCategory.middleRightRestrictionCompositeMap, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, bimoduleDerivedIso, Localization.Construction.wIso,
    CategoryTheory.Functor.map_comp, NatTrans.comp_app,
    BimoduleCategory.middleRightRestrictionCompIso, BimoduleCategory.middleLeftRestrictionCompIso,
    NatIso.ofComponents_hom_app, bimoduleToDerived, Category.assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleAugmentedSource

/-! ## BimoduleMiddleAugmentedTransport（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleAugmentedTransport.lean） -/

/-! # 指定増大による二段階sourceと移送計算の接続

## 概要
指定増大による二段階sourceと移送計算の接続。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleAugmentedTransport
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor

private lemma bifunctor_transport
    {C D E : Type*} [Category* C] [Category* D] [Category* E] (H : C ⥤ D ⥤ E)
    {r₀ r₁ r₂ r₃ r₄ : C} {l₀ l₁ l₂ : D}
    (c : r₀ ⟶ r₁) (a : r₀ ⟶ r₂) (b : r₁ ⟶ r₃) (d : r₂ ⟶ r₃) (e : r₃ ⟶ r₄)
    (x : l₀ ⟶ l₁) (y : l₁ ⟶ l₂) (hr : c ≫ b = a ≫ d) :
    (H.map c).app l₀ ≫ (H.obj r₁).map x ≫ (H.obj r₁).map y ≫
        (H.map b).app l₂ ≫ (H.map e).app l₂ =
      (H.obj r₀).map x ≫ (H.map a).app l₁ ≫ (H.map d).app l₁ ≫
        (H.map e).app l₁ ≫ (H.obj r₄).map y := by
  have hrt : c ≫ b ≫ e = a ≫ d ≫ e := by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ e) hr
  calc
    _ = (H.obj r₀).map x ≫ (H.obj r₀).map y ≫ (H.map (c ≫ b ≫ e)).app l₂ := by
      simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app]
      rw [← (H.map c).naturality_assoc, ← (H.map c).naturality_assoc]
    _ = (H.obj r₀).map x ≫ (H.obj r₀).map y ≫ (H.map (a ≫ d ≫ e)).app l₂ := by rw [hrt]
    _ = _ := by
      rw [(H.map (a ≫ d ≫ e)).naturality y]
      simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]

variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

/-- 指定増大によるsource射は、前段比較のsourceを両変数で移送する射に一致する。 -/
lemma middleIteratedAugmentedSourceMap_transport
    (Q : BimoduleCategory A T L) (P : BimoduleCategory A B T)
    (R : RightKFlatBimoduleCategory A E L)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q) :
    middleIteratedAugmentedSourceMap A B D E T L F G hL Q P R.obj q =
      (middleDerivedSourceFamilyIdentification A B E D L F hL R).hom.app
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P) ≫
        ((middleRestrictionDerivedSource A B E D L F hL).map
          ((bimoduleToDerived A E L).map q ≫
            (middleRightRestrictionDerivedIso A T E G L).hom.app Q)).app
          ((bimoduleToDerived A B E).obj
            ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)) ≫
        ((middleRestrictionDerivedSource A B E D L F hL).obj
          ((derivedBimoduleRestriction A E L T L G (DGFunctor.id L)).obj
            ((bimoduleToDerived A T L).obj Q))).map
          ((middleLeftRestrictionDerivedIso A B T E G).hom.app P) := by
  have hr := (middleRightRestrictionDerivedIso A E D F L).hom.naturality q
  simp only [Functor.comp_map] at hr
  have h := bifunctor_transport (derivedBimoduleComposeFunctor A B D L hL)
    ((bimoduleToDerived A D L).map
      ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).map q))
    ((middleRightRestrictionDerivedIso A E D F L).hom.app R.obj)
    ((middleRightRestrictionDerivedIso A E D F L).hom.app
      ((BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q))
    ((derivedBimoduleRestriction A D L E L F (DGFunctor.id L)).map
      ((bimoduleToDerived A E L).map q))
    ((derivedBimoduleRestriction A D L E L F (DGFunctor.id L)).map
      ((middleRightRestrictionDerivedIso A T E G L).hom.app Q))
    ((middleLeftRestrictionDerivedIso A B E D F).hom.app
      ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))
    ((derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map
      ((middleLeftRestrictionDerivedIso A B T E G).hom.app P)) hr
  simpa only [middleIteratedAugmentedSourceMap, middleIteratedClosedSourceIso,
    middleLeftIteratedDerivedIso, middleRightIteratedDerivedIso,
    middleDerivedSourceFamilyIdentification, middleClosedSourceIdentification,
    middleRestrictionDerivedSource, Iso.trans_hom, Iso.app_hom, NatTrans.comp_app,
    Functor.mapIso_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, whiskeringLeft, Functor.comp_map, Functor.comp_obj,
    CategoryTheory.Functor.map_comp, Category.assoc] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleAugmentedTransport

/-! ## BimoduleMiddleIteratedComputation（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleIteratedComputation.lean） -/

/-! # 二段階全導来比較を指定K-flatモデルと増大で計算する

## 概要
二段階全導来比較を指定K-flatモデルと増大で計算する。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleIteratedComputation
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

/-- 増大に準同型性を課さず、二段階比較を任意の右K-flatモデル上で計算する。 -/
lemma middleIteratedAugmentedComparison_fac
    (Q : RightKFlatBimoduleCategory A T L) (P : BimoduleCategory A B T)
    (R : RightKFlatBimoduleCategory A E L)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q.obj) :
    middleIteratedAugmentedSourceMap A B D E T L F G hL Q.obj P R.obj q ≫
        ((middleIteratedDerivedComparison A B D E T L F G hL).app
          ((bimoduleToDerived A T L).obj Q.obj)).app ((bimoduleToDerived A B T).obj P) =
      derivedMiddleRestrictionCanonicalComparison A B E D L F hL
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P) R ≫
        ((derivedBimoduleComposeFunctor A B E L hL).map ((bimoduleToDerived A E L).map q)).app
          ((bimoduleToDerived A B E).obj
            ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)) ≫
        derivedMiddleRestrictionCanonicalComparison A B T E L G hL P Q := by
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P
  let Q' := (derivedBimoduleRestriction A E L T L G (DGFunctor.id L)).obj
    ((bimoduleToDerived A T L).obj Q.obj)
  let P' := (derivedBimoduleRestriction A B E B T (DGFunctor.id B) G).obj
    ((bimoduleToDerived A B T).obj P)
  let g := (bimoduleToDerived A E L).map q ≫
    (middleRightRestrictionDerivedIso A T E G L).hom.app Q.obj
  let f := (middleLeftRestrictionDerivedIso A B T E G).hom.app P
  have he :
      ((derivedBimoduleComposeFunctor A B E L hL).map
          ((middleRightRestrictionDerivedIso A T E G L).hom.app Q.obj)).app
          ((bimoduleToDerived A B E).obj P₀) ≫
        ((derivedBimoduleComposeFunctor A B E L hL).obj Q').map f =
      (middleDerivedSourceFamilyIdentification A B T E L G hL Q).hom.app P := by
    have hn := ((derivedBimoduleComposeFunctor A B E L hL).map
      ((middleRightRestrictionDerivedIso A T E G L).hom.app Q.obj)).naturality f
    simpa only [middleDerivedSourceFamilyIdentification, middleClosedSourceIdentification,
      Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Functor.mapIso_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, whiskerLeft_app,
      whiskerRight_app, whiskeringLeft, Functor.comp_obj, Functor.comp_map] using hn.symm
  have h := derivedMiddleRestrictionNatTrans_transport_fac A B E D L F hL R P₀ Q' P' g f
  calc
    _ = (derivedMiddleRestrictionCanonicalComparison A B E D L F hL P₀ R ≫
        ((derivedBimoduleComposeFunctor A B E L hL).map g).app
          ((bimoduleToDerived A B E).obj P₀) ≫
        ((derivedBimoduleComposeFunctor A B E L hL).obj Q').map f) ≫
      ((derivedMiddleRestrictionNatTrans A B T E L G hL).app
        ((bimoduleToDerived A T L).obj Q.obj)).app ((bimoduleToDerived A B T).obj P) := by
      simpa only [middleIteratedDerivedComparison_app,
        middleIteratedAugmentedSourceMap_transport, Category.assoc] using
        congrArg (fun k => k ≫ ((derivedMiddleRestrictionNatTrans A B T E L G hL).app
          ((bimoduleToDerived A T L).obj Q.obj)).app ((bimoduleToDerived A B T).obj P)) h
    _ = _ := by
      dsimp only [g]
      rw [CategoryTheory.Functor.map_comp, NatTrans.comp_app]
      simp only [Category.assoc]
      rw [← Category.assoc _ _
        (((derivedMiddleRestrictionNatTrans A B T E L G hL).app
          ((bimoduleToDerived A T L).obj Q.obj)).app ((bimoduleToDerived A B T).obj P)), he]
      rw [derivedMiddleRestrictionNatTrans_base_fac]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleIteratedComputation

/-! ## BimoduleMiddleFullComposition（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleFullComposition.lean） -/

/-! # 中間dg圏制限の合成則を両変数の全導来圏へ降ろす

## 概要
中間dg圏制限の合成則を両変数の全導来圏へ降ろす。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleFullComposition
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

/-- 実際の二段階全導来比較は、合成dg関手の比較と独立に構成したsource正規化の合成に一致。 -/
lemma derivedMiddleRestrictionNatTrans_functor_comp :
    (middleIteratedDerivedSourceIso A B D E T L F G hL).hom ≫
        derivedMiddleRestrictionNatTrans A B T D L (F.comp G) hL =
      middleIteratedDerivedComparison A B D E T L F G hL := by
  apply middleDerivedFamily_ext A B T L hL
  intro Q P
  let R := bimoduleCanonicalSemifreeResolution A E L
    ((BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q.obj)
  let Rf := R.toRightKFlat A E L hL
  let a := middleIteratedAugmentedSourceMap A B D E T L F G hL Q.obj P R.obj R.π
  have hq : BimoduleCategory.quasiIso A D L
      ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).map R.π) := by
    intro d l
    change QuasiIso ((BimoduleCategory.valueEvaluation A D L d l).map
      (BimoduleCategory.middleRightRestrictionMap A E D L F R.π))
    rw [BimoduleCategory.middleRightRestrictionMap_value_eval]
    exact R.quasiIso (F.obj d) l
  have hi := bimoduleToDerived_inverts A D L _ hq
  have ha : IsIso a := by
    dsimp only [a, middleIteratedAugmentedSourceMap]
    infer_instance
  apply (cancel_epi a).mp
  simp only [NatTrans.comp_app]
  calc
    _ = (derivedMiddleCompositeSourceIso A B D L hL E T F G P Q.obj R.obj R.π
        R.quasiIso).hom ≫
        derivedMiddleRestrictionCanonicalComparison A B T D L (F.comp G) hL P Q := by
      dsimp only [a]
      rw [← Category.assoc, middleIteratedAugmentedSourceMap_normalize, Category.assoc]
      exact congrArg (fun f =>
        (derivedMiddleCompositeSourceIso A B D L hL E T F G P Q.obj R.obj R.π
          R.quasiIso).hom ≫ f)
        (derivedMiddleRestrictionNatTrans_base_fac A B T D L (F.comp G) hL Q P)
    _ = derivedMiddleRestrictionCanonicalComparison A B E D L F hL
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P) Rf ≫
        ((derivedBimoduleComposeFunctor A B E L hL).map ((bimoduleToDerived A E L).map R.π)).app
          ((bimoduleToDerived A B E).obj
            ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)) ≫
        derivedMiddleRestrictionCanonicalComparison A B T E L G hL P Q :=
      derivedMiddleRestrictionCanonicalComparison_functor_comp A B D E T L F G hL P Q
    _ = _ := (middleIteratedAugmentedComparison_fac A B D E T L F G hL Q P Rf R.π).symm

/-- 合成則の成分式は両変数とも任意の導来対象に適用できる。 -/
lemma derivedMiddleRestrictionNatTrans_functor_comp_app
    (Q : DerivedBimoduleCategory A T L) (P : DerivedBimoduleCategory A B T) :
    ((middleIteratedDerivedSourceIso A B D E T L F G hL).hom.app Q).app P ≫
        ((derivedMiddleRestrictionNatTrans A B T D L (F.comp G) hL).app Q).app P =
      ((derivedMiddleRestrictionNatTrans A B E D L F hL).app
          ((derivedBimoduleRestriction A E L T L G (DGFunctor.id L)).obj Q)).app
          ((derivedBimoduleRestriction A B E B T (DGFunctor.id B) G).obj P) ≫
        ((derivedMiddleRestrictionNatTrans A B T E L G hL).app Q).app P := by
  simpa only [NatTrans.comp_app, middleIteratedDerivedComparison_app] using
    NatTrans.congr_app (NatTrans.congr_app
      (derivedMiddleRestrictionNatTrans_functor_comp A B D E T L F G hL) Q) P

/-- 二つの準同値に対する、既存の比較自然同型を実際に二段階で適用する同型。 -/
def middleIteratedDerivedIso (hF : QuasiEquivalence F) (hG : QuasiEquivalence G) :
    middleIteratedDerivedSource A B D E T L F G hL ≅
      derivedBimoduleComposeFunctor A B T L hL :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (derivedBimoduleRestriction A E L T L G (DGFunctor.id L))
        (derivedMiddleRestrictionIso A B E D L F hF hL))
      ((Functor.whiskeringLeft _ _ _).obj
        (derivedBimoduleRestriction A B E B T (DGFunctor.id B) G)) ≪≫
    derivedMiddleRestrictionIso A B T E L G hG hL

/-- 準同値の場合の自然同型そのものの推移整合性。 -/
lemma derivedMiddleRestrictionIso_functor_comp
    (hF : QuasiEquivalence F) (hG : QuasiEquivalence G) :
    middleIteratedDerivedSourceIso A B D E T L F G hL ≪≫
        derivedMiddleRestrictionIso A B T D L (F.comp G)
          (quasiEquivalence_comp F G hF hG) hL =
      middleIteratedDerivedIso A B D E T L F G hL hF hG := by
  apply Iso.ext
  simpa only [Iso.trans_hom, middleIteratedDerivedIso,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    derivedMiddleRestrictionIso_hom, middleIteratedDerivedComparison] using
    derivedMiddleRestrictionNatTrans_functor_comp A B D E T L F G hL

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleFullComposition
