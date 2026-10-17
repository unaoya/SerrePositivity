module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorKFlat
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionLeftUnitComputation
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorTriangle

/-! # 全導来合成の三角恒等式のK-flat因子での比較

## 概要
全導来合成の三角恒等式のK-flat因子での比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionTriangleFamily.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
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

lemma derivedBimoduleTriangle_kFlat (hC : localHomKFlat A C) (hE : localHomKFlat A E)
    (Q : RightKFlatBimoduleCategory A C E) :
    (((derivedBimoduleAssociatorIso A B C C E hC hE).app
        ((bimoduleToDerived A C E).obj Q.obj)).app
          ((bimoduleToDerived A C C).obj (rightKFlatDiagonal A C).obj)).hom ≫
      (derivedBimoduleComposeFunctor A B C E hE).map
        ((derivedBimoduleLeftUnitIso A C E hE).hom.app ((bimoduleToDerived A C E).obj Q.obj)) =
    whiskerRight (derivedBimoduleRightUnitIso A B C hC).hom
        ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj)) ≫
      (Functor.leftUnitor ((derivedBimoduleComposeFunctor A B C E hE).obj
        ((bimoduleToDerived A C E).obj Q.obj))).hom := by
  let Δ := rightKFlatDiagonal A C
  let U := rightKFlatCompose A C C E Δ Q
  let u : U ⟶ Q :=
    ⟨(leftBimoduleUnitIso A C E (BimoduleCategory.underlying A C E Q.obj)).hom⟩
  have hn := derivedBimoduleComposeKFlatIso_naturality A B C E hE u
  have ha := derivedBimoduleAssociatorIso_kFlat_fac A B C C E hC hE Δ Q
  have ht := derivedTriangle A B C E Q.obj Q.property
  change (rightKFlatDerivedAssociator A B C C E Δ Q).hom ≫
    derivedComposeWithMap A B C E U.property Q.property u.hom = _ at ht
  apply (Iso.cancel_iso_hom_right _ _ (derivedBimoduleComposeKFlatIso A B C E hE Q)).1
  rw [derivedBimoduleLeftUnitIso_kFlat_base_app, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [hn]
  simp only [← Category.assoc] at ha ⊢
  rw [ha]
  simp only [Category.assoc]
  rw [ht]
  ext P
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.leftUnitor_hom_app,
    ]
  have hx := (derivedBimoduleComposeKFlatIso A B C E hE Q).hom.naturality
    ((derivedRightUnitIso A B C).hom.app P)
  let FQ := (derivedBimoduleComposeFunctor A B C E hE).obj
    ((bimoduleToDerived A C E).obj Q.obj)
  let KQ := derivedComposeWith A B C E Q.obj Q.property
  let c := (derivedBimoduleComposeKFlatIso A B C E hE Q).hom
  let a := (derivedBimoduleComposeKFlatIso A B C C hC Δ).hom.app P
  let r := (derivedRightUnitIso A B C).hom.app P
  change FQ.map a ≫ (c.app _ ≫ (KQ.map r ≫ 𝟙 (KQ.obj P))) =
    FQ.map ((derivedBimoduleRightUnitIso A B C hC).hom.app P) ≫
      (𝟙 (FQ.obj P) ≫ c.app P)
  change FQ.map r ≫ c.app P = c.app _ ≫ KQ.map r at hx
  calc
    _ = FQ.map a ≫ (c.app _ ≫ KQ.map r) :=
      congrArg (fun k => FQ.map a ≫ (c.app _ ≫ k)) (Category.comp_id (KQ.map r))
    _ = FQ.map a ≫ (FQ.map r ≫ c.app P) := congrArg (fun k => FQ.map a ≫ k) hx.symm
    _ = (FQ.map a ≫ FQ.map r) ≫ c.app P := (Category.assoc _ _ _).symm
    _ = FQ.map (a ≫ r) ≫ c.app P := congrArg (fun k => k ≫ c.app P) (FQ.map_comp a r).symm
    _ = _ := (congrArg (fun k => FQ.map (a ≫ r) ≫ k) (Category.id_comp (c.app P))).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
