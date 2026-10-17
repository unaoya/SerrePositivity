module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionTriangle

/-! # 三角恒等式の両経路を束ねる全導来自然変換

## 概要
三角恒等式の両経路を束ねる全導来自然変換。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleLocal.lean。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

def derivedBimoduleTriangleSource (hC : localHomKFlat A C) (hE : localHomKFlat A E) :
    DerivedBimoduleCategory A C E ⥤
      (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  derivedBimoduleComposeFunctor A B C E hE ⋙
    (whiskeringLeft (DerivedBimoduleCategory A B C) (DerivedBimoduleCategory A B C)
      (DerivedBimoduleCategory A B E)).obj
        ((derivedBimoduleComposeFunctor A B C C hC).obj
          ((bimoduleToDerived A C C).obj (rightKFlatDiagonal A C).obj))

def derivedBimoduleTriangleLeft (hC : localHomKFlat A C) (hE : localHomKFlat A E) :
    derivedBimoduleTriangleSource A B C E hC hE ⟶ derivedBimoduleComposeFunctor A B C E hE :=
  whiskerRight (derivedBimoduleAssociatorIso A B C C E hC hE).hom
      ((CategoryTheory.evaluation (DerivedBimoduleCategory A C C)
        (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E)).obj
          ((bimoduleToDerived A C C).obj (rightKFlatDiagonal A C).obj)) ≫
    whiskerRight (derivedBimoduleLeftUnitIso A C E hE).hom
      (derivedBimoduleComposeFunctor A B C E hE)

def derivedBimoduleTriangleRight (hC : localHomKFlat A C) (hE : localHomKFlat A E) :
    derivedBimoduleTriangleSource A B C E hC hE ⟶ derivedBimoduleComposeFunctor A B C E hE :=
  whiskerLeft (derivedBimoduleComposeFunctor A B C E hE)
    ((whiskeringLeft (DerivedBimoduleCategory A B C) (DerivedBimoduleCategory A B C)
      (DerivedBimoduleCategory A B E)).map (derivedBimoduleRightUnitIso A B C hC).hom)

lemma derivedBimoduleTriangleFamily_kFlat (hC : localHomKFlat A C)
    (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E) :
    (derivedBimoduleTriangleLeft A B C E hC hE).app ((bimoduleToDerived A C E).obj Q.obj) =
      (derivedBimoduleTriangleRight A B C E hC hE).app ((bimoduleToDerived A C E).obj Q.obj) := by
  have h := derivedBimoduleTriangle_kFlat A B C E hC hE Q
  ext P
  have hp := NatTrans.congr_app h P
  simp only [NatTrans.comp_app, Functor.leftUnitor_hom_app] at hp
  change _ ≫ _ = _ ≫ 𝟙 _ at hp
  exact hp.trans (Category.comp_id _)

/-- 三角図式は後因子の全指定局所化上の自然変換として可換。 -/
lemma derivedBimoduleTriangle (hC : localHomKFlat A C) (hE : localHomKFlat A E) :
    derivedBimoduleTriangleLeft A B C E hC hE =
      derivedBimoduleTriangleRight A B C E hC hE := by
  let J := rightKFlatDerivedInclusion A C E
  let : J.EssSurj := rightKFlatDerivedInclusion_essSurj A C E hE
  have hJ : whiskerLeft J (derivedBimoduleTriangleLeft A B C E hC hE) =
      whiskerLeft J (derivedBimoduleTriangleRight A B C E hC hE) := by
    apply Localization.natTrans_ext (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
    intro Q
    exact derivedBimoduleTriangleFamily_kFlat A B C E hC hE Q
  apply NatTrans.ext
  funext Q
  let e := J.objObjPreimageIso Q
  have hx := NatTrans.congr_app hJ (J.objPreimage Q)
  change (derivedBimoduleTriangleLeft A B C E hC hE).app (J.obj (J.objPreimage Q)) =
    (derivedBimoduleTriangleRight A B C E hC hE).app (J.obj (J.objPreimage Q)) at hx
  apply (Iso.cancel_iso_hom_left
    ((derivedBimoduleTriangleSource A B C E hC hE).mapIso e) _ _).1
  change (derivedBimoduleTriangleSource A B C E hC hE).map e.hom ≫ _ =
    (derivedBimoduleTriangleSource A B C E hC hE).map e.hom ≫ _
  rw [(derivedBimoduleTriangleLeft A B C E hC hE).naturality,
    (derivedBimoduleTriangleRight A B C E hC hE).naturality, hx]

/-- 任意の導来後因子について、結合比較と左単位の経路は右単位の経路に一致する。 -/
lemma derivedBimoduleTriangle_app (hC : localHomKFlat A C) (hE : localHomKFlat A E)
    (Q : DerivedBimoduleCategory A C E) :
    (((derivedBimoduleAssociatorIso A B C C E hC hE).app Q).app
        ((bimoduleToDerived A C C).obj (rightKFlatDiagonal A C).obj)).hom ≫
      (derivedBimoduleComposeFunctor A B C E hE).map
        ((derivedBimoduleLeftUnitIso A C E hE).hom.app Q) =
    whiskerRight (derivedBimoduleRightUnitIso A B C hC).hom
      ((derivedBimoduleComposeFunctor A B C E hE).obj Q) :=
  NatTrans.congr_app (derivedBimoduleTriangle A B C E hC hE) Q

end SerrePositivity.DifferentialGraded.BimoduleTensor
