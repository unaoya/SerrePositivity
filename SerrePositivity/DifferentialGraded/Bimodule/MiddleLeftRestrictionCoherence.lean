module
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionMaps
public import SerrePositivity.DifferentialGraded.Bimodule.ValueIsomorphism
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation

/-! # 左側の中間制限の恒等・合成自然同型

## 概要
左側の中間制限の恒等・合成自然同型。

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
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D]

/-- 恒等dg関手に沿う直接の左制限は、右加群ごとに恒等となる同型で元に戻る。 -/
def middleLeftRestrictionIdObjIso (P : BimoduleCategory A B D) :
    (middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P ≅ P :=
  isoOfValueFamily A B D
    (M := (middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P) (N := P)
    (fun d => Iso.refl ((evaluation A B D d).obj P)) (by
    intro b d d'
    change ((underlying A B D
      ((middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P)).leftAt b).map d d' ≫
      homPostcompose ((underlying A B D P).value b d)
        ((moduleEvaluation A B b).map
          (X := (evaluation A B D d').obj P) (Y := (evaluation A B D d').obj P) (𝟙 _)) =
      ((underlying A B D P).leftAt b).map d d' ≫
        homPrecompose ((moduleEvaluation A B b).map
          (X := (evaluation A B D d).obj P) (Y := (evaluation A B D d).obj P) (𝟙 _))
          ((underlying A B D P).value b d')
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    apply hom_naturality_of_apply
    intro p f
    refine (Cochain.comp_id _).trans ?_
    refine Eq.trans ?_ (Cochain.id_comp _).symm
    have hh :
        (Bimodule.leftAt (underlying A B D
          ((middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P)) b).map d d' =
          ((underlying A B D P).leftAt b).map d d' := by
      change ((𝟙 _ ≫ (underlying A B D P).map d d') ≫ moduleHomπ A B _ _ b) =
        (underlying A B D P).map d d' ≫ moduleHomπ A B _ _ b
      rw [Category.id_comp]
    exact congrArg (fun k => k.f p f) hh)

@[simp]
lemma middleLeftRestrictionIdObjIso_hom_eval (P : BimoduleCategory A B D) (d : D) :
    (evaluation A B D d).map (middleLeftRestrictionIdObjIso A B D P).hom = 𝟙 _ := rfl

/-- 直接の左制限の恒等比較は任意の閉零bimodule射に自然。 -/
def middleLeftRestrictionIdIso :
    middleLeftRestrictionFunctor A B D D (DGFunctor.id D) ≅ 𝟭 (BimoduleCategory A B D) :=
  NatIso.ofComponents (middleLeftRestrictionIdObjIso A B D) (by
    intro P P' f
    apply hom_ext
    intro d
    change f.val d ≫ 𝟙 _ = 𝟙 _ ≫ f.val d
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

variable (E : Type z) [DGCategory A E] (T : Type t) [DGCategory A T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 二段階の左制限と合成dg関手による左制限の、右加群ごとに恒等となる同型。 -/
def middleLeftRestrictionCompObjIso (P : BimoduleCategory A B T) :
    (middleLeftRestrictionFunctor A B E D F).obj
        ((middleLeftRestrictionFunctor A B T E G).obj P) ≅
      (middleLeftRestrictionFunctor A B T D (F.comp G)).obj P :=
  isoOfValueFamily A B D
    (M := (middleLeftRestrictionFunctor A B E D F).obj
      ((middleLeftRestrictionFunctor A B T E G).obj P))
    (N := (middleLeftRestrictionFunctor A B T D (F.comp G)).obj P)
    (fun d => Iso.refl ((evaluation A B T (G.obj (F.obj d))).obj P)) (by
    intro b d d'
    change ((underlying A B D ((middleLeftRestrictionFunctor A B E D F).obj
      ((middleLeftRestrictionFunctor A B T E G).obj P))).leftAt b).map d d' ≫
      homPostcompose ((underlying A B T P).value b (G.obj (F.obj d)))
        ((moduleEvaluation A B b).map
          (X := (evaluation A B T (G.obj (F.obj d'))).obj P)
          (Y := (evaluation A B T (G.obj (F.obj d'))).obj P) (𝟙 _)) =
      (Bimodule.leftAt (underlying A B D
        ((middleLeftRestrictionFunctor A B T D (F.comp G)).obj P)) b).map d d' ≫
        homPrecompose ((moduleEvaluation A B b).map
          (X := (evaluation A B T (G.obj (F.obj d))).obj P)
          (Y := (evaluation A B T (G.obj (F.obj d))).obj P) (𝟙 _))
          ((underlying A B T P).value b (G.obj (F.obj d')))
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    apply hom_naturality_of_apply
    intro p f
    refine (Cochain.comp_id _).trans ?_
    refine Eq.trans ?_ (Cochain.id_comp _).symm
    have hh :
        ((underlying A B D ((middleLeftRestrictionFunctor A B E D F).obj
          ((middleLeftRestrictionFunctor A B T E G).obj P))).leftAt b).map d d' =
        (Bimodule.leftAt (underlying A B D
          ((middleLeftRestrictionFunctor A B T D (F.comp G)).obj P)) b).map d d' := by
      change ((F.map d d' ≫ (G.map (F.obj d) (F.obj d') ≫
        (underlying A B T P).map (G.obj (F.obj d)) (G.obj (F.obj d')))) ≫
          moduleHomπ A B _ _ b) =
        (((F.map d d' ≫ G.map (F.obj d) (F.obj d')) ≫
          (underlying A B T P).map (G.obj (F.obj d)) (G.obj (F.obj d'))) ≫
            moduleHomπ A B _ _ b)
      simp only [Category.assoc]
    exact congrArg (fun k => k.f p f) hh)

@[simp]
lemma middleLeftRestrictionCompObjIso_hom_eval (P : BimoduleCategory A B T) (d : D) :
    (evaluation A B D d).map (middleLeftRestrictionCompObjIso A B D E T F G P).hom = 𝟙 _ := rfl

/-- 二段階の直接左制限の比較は任意の閉零bimodule射に自然。 -/
def middleLeftRestrictionCompIso :
    middleLeftRestrictionFunctor A B T E G ⋙ middleLeftRestrictionFunctor A B E D F ≅
      middleLeftRestrictionFunctor A B T D (F.comp G) :=
  NatIso.ofComponents (middleLeftRestrictionCompObjIso A B D E T F G) (by
    intro P P' f
    apply hom_ext
    intro d
    change f.val (G.obj (F.obj d)) ≫ 𝟙 _ = 𝟙 _ ≫ f.val (G.obj (F.obj d))
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

end SerrePositivity.DifferentialGraded.BimoduleCategory
