module
public import SerrePositivity.DifferentialGraded.Bimodule.ExplicitRightModuleFunctor
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionMaps
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionUncurry
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestriction

/-! # 左右の中間制限と積dg圏上の明示的右加群表示の比較

## 概要
左右の中間制限と積dg圏上の明示的右加群表示の比較。

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
namespace SerrePositivity.DifferentialGraded.BimoduleTensorModule
open CategoryTheory Opposite MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D C)

/-- 左制限の両表示は値で恒等の全Hom自然な右加群同型で結ばれる。 -/
def middleLeftPresentationObjIso (P : BimoduleCategory A B C) :
    (rightModuleFunctor A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P) ≅
      (moduleRestriction A (DGTensorCategory A Bᵒᵖ D)ᵒᵖ
        (DGTensorCategory A Bᵒᵖ C)ᵒᵖ ((DGFunctor.id Bᵒᵖ).tensor F).op.op).obj
        ((rightModuleFunctor A B C).obj P) :=
  moduleIsoMk A (DGTensorCategory A Bᵒᵖ D)ᵒᵖ (fun _ => Iso.refl _) (by
    intro x y
    apply hom_naturality_of_apply
    intro p f
    refine (CochainComplex.HomComplex.Cochain.comp_id _).trans ?_
    refine Eq.trans ?_ (CochainComplex.HomComplex.Cochain.id_comp _).symm
    change ((𝟙 _ ≫
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)).uncurryHom
        x.unop.unop y.unop.unop).f p f) =
      (((𝟙 _ ⊗ₘ F.map x.unop.unop.2 y.unop.unop.2) ≫
        (𝟙 _ ≫ (BimoduleCategory.underlying A B C P).uncurryHom
          (x.unop.unop.1, F.obj x.unop.unop.2)
          (y.unop.unop.1, F.obj y.unop.unop.2))).f p f)
    simp only [Category.id_comp]
    exact congrArg (fun k => k.f p f)
      (Bimodule.leftRestriction_uncurryHom A B C D F
        (BimoduleCategory.underlying A B C P) x.unop.unop y.unop.unop))

@[simp]
lemma middleLeftPresentationObjIso_hom_eval (P : BimoduleCategory A B C)
    (x : (DGTensorCategory A Bᵒᵖ D)ᵒᵖ) :
    (moduleEvaluation A (DGTensorCategory A Bᵒᵖ D)ᵒᵖ x).map
      (middleLeftPresentationObjIso A B C D F P).hom = 𝟙 _ :=
  moduleIsoMk_hom_eval A (DGTensorCategory A Bᵒᵖ D)ᵒᵖ _ _ x

/-- 明示的表示の左制限squareは任意の閉零bimodule射について自然。 -/
def middleLeftPresentationIso :
    BimoduleCategory.middleLeftRestrictionFunctor A B C D F ⋙ rightModuleFunctor A B D ≅
      rightModuleFunctor A B C ⋙
        moduleRestriction A (DGTensorCategory A Bᵒᵖ D)ᵒᵖ (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
          ((DGFunctor.id Bᵒᵖ).tensor F).op.op :=
  NatIso.ofComponents (middleLeftPresentationObjIso A B C D F) (by
    intro P P' f
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, middleLeftPresentationObjIso_hom_eval,
      Functor.comp_map]
    have h := rightModuleFunctor_map_value A B D
      ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).map f)
      x.unop.1.unop x.unop.2
    have h' := moduleRestriction_map_eval A (DGTensorCategory A Bᵒᵖ D)ᵒᵖ
      (DGTensorCategory A Bᵒᵖ C)ᵒᵖ ((DGFunctor.id Bᵒᵖ).tensor F).op.op
      ((rightModuleFunctor A B C).map f) x
    exact h.trans ((BimoduleCategory.middleLeftRestrictionMap_value_eval A B C D F f
      x.unop.1.unop x.unop.2).trans
        ((rightModuleFunctor_map_value A B C f x.unop.1.unop (F.obj x.unop.2)).symm.trans
          h'.symm)))

variable (E : Type t) [DGCategory A E] [Small.{u} E]

/-- 右制限の両表示も各値で恒等となる全Hom自然な右加群同型。 -/
def middleRightPresentationObjIso (Q : BimoduleCategory A C E) :
    (rightModuleFunctor A D E).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q) ≅
      (moduleRestriction A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
        (DGTensorCategory A Cᵒᵖ E)ᵒᵖ (F.op.tensor (DGFunctor.id E)).op.op).obj
        ((rightModuleFunctor A C E).obj Q) :=
  moduleIsoMk A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (fun _ => Iso.refl _) (by
    intro x y
    apply hom_naturality_of_apply
    intro p f
    refine (CochainComplex.HomComplex.Cochain.comp_id _).trans ?_
    refine Eq.trans ?_ (CochainComplex.HomComplex.Cochain.id_comp _).symm
    change ((𝟙 _ ≫
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q)).uncurryHom
        x.unop.unop y.unop.unop).f p f) =
      (((F.op.map x.unop.unop.1 y.unop.unop.1 ⊗ₘ 𝟙 _) ≫
        (𝟙 _ ≫ (BimoduleCategory.underlying A C E Q).uncurryHom
          (F.op.obj x.unop.unop.1, x.unop.unop.2)
          (F.op.obj y.unop.unop.1, y.unop.unop.2))).f p f)
    simp only [Category.id_comp]
    exact congrArg (fun k => k.f p f)
      (Bimodule.rightRestriction_uncurryHom A C D E F
        (BimoduleCategory.underlying A C E Q) x.unop.unop y.unop.unop))

@[simp]
lemma middleRightPresentationObjIso_hom_eval (Q : BimoduleCategory A C E)
    (x : (DGTensorCategory A Dᵒᵖ E)ᵒᵖ) :
    (moduleEvaluation A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ x).map
      (middleRightPresentationObjIso A C D F E Q).hom = 𝟙 _ :=
  moduleIsoMk_hom_eval A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ _ _ x

/-- 明示的表示の右制限squareは任意の閉零bimodule射について自然。 -/
def middleRightPresentationIso :
    BimoduleCategory.middleRightRestrictionFunctor A C D E F ⋙ rightModuleFunctor A D E ≅
      rightModuleFunctor A C E ⋙
        moduleRestriction A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (DGTensorCategory A Cᵒᵖ E)ᵒᵖ
          (F.op.tensor (DGFunctor.id E)).op.op :=
  NatIso.ofComponents (middleRightPresentationObjIso A C D F E) (by
    intro Q Q' f
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, middleRightPresentationObjIso_hom_eval,
      Functor.comp_map]
    have h := rightModuleFunctor_map_value A D E
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).map f)
      x.unop.1.unop x.unop.2
    have h' := moduleRestriction_map_eval A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
      (DGTensorCategory A Cᵒᵖ E)ᵒᵖ (F.op.tensor (DGFunctor.id E)).op.op
      ((rightModuleFunctor A C E).map f) x
    exact h.trans ((BimoduleCategory.middleRightRestrictionMap_value_eval A C D E F f
      x.unop.1.unop x.unop.2).trans
        ((rightModuleFunctor_map_value A C E f (F.obj x.unop.1.unop) x.unop.2).symm.trans
          h'.symm)))

end SerrePositivity.DifferentialGraded.BimoduleTensorModule
