module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleQuasiIso
public import SerrePositivity.DifferentialGraded.Bimodule.ResolvedRestrictionAugmentation
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleLeftRestrictionCoherence

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
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
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
