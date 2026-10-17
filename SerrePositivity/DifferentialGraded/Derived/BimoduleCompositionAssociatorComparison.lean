module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorComponents

/-! # 導来同型で指定されたK-flat代表と結合同型の比較

## 概要
導来同型で指定されたK-flat代表と結合同型の比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPentagonPaths.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

def derivedBimoduleComposePairComparisonIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) {Q : DerivedBimoduleCategory A C E}
    {R : DerivedBimoduleCategory A E F}
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : Q ≅ (bimoduleToDerived A C E).obj S.obj)
    (r : R ≅ (bimoduleToDerived A E F).obj T.obj) :
    (derivedBimoduleComposeFunctor A B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R ≅
      derivedComposeWith A B C E S.obj S.property ⋙
        derivedComposeWith A B E F T.obj T.property :=
  isoWhiskerRight ((derivedBimoduleComposeFunctor A B C E hE).mapIso q)
      ((derivedBimoduleComposeFunctor A B E F hF).obj R) ≪≫
    isoWhiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj
        ((bimoduleToDerived A C E).obj S.obj))
      ((derivedBimoduleComposeFunctor A B E F hF).mapIso r) ≪≫
    isoWhiskerRight (derivedBimoduleComposeKFlatIso A B C E hE S)
      ((derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj T.obj)) ≪≫
    isoWhiskerLeft (derivedComposeWith A B C E S.obj S.property)
      (derivedBimoduleComposeKFlatIso A B E F hF T)

def derivedBimoduleComposeInnerComparisonIso (hF : localHomKFlat A F)
    {Q : DerivedBimoduleCategory A C E} {R : DerivedBimoduleCategory A E F}
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : Q ≅ (bimoduleToDerived A C E).obj S.obj)
    (r : R ≅ (bimoduleToDerived A E F).obj T.obj) :
    ((derivedBimoduleComposeFunctor A C E F hF).obj R).obj Q ≅
      (bimoduleToDerived A C F).obj (rightKFlatCompose A C E F S T).obj :=
  ((derivedBimoduleComposeFunctor A C E F hF).obj R).mapIso q ≪≫
    ((derivedBimoduleComposeFunctor A C E F hF).mapIso r).app
      ((bimoduleToDerived A C E).obj S.obj) ≪≫
    derivedBimoduleComposeKFlatValueIso A C E F hF T S.obj

def derivedBimoduleComposeNestedComparisonIso (hF : localHomKFlat A F)
    {Q : DerivedBimoduleCategory A C E} {R : DerivedBimoduleCategory A E F}
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : Q ≅ (bimoduleToDerived A C E).obj S.obj)
    (r : R ≅ (bimoduleToDerived A E F).obj T.obj) :
    (derivedBimoduleComposeFunctor A B C F hF).obj
        (((derivedBimoduleComposeFunctor A C E F hF).obj R).obj Q) ≅
      derivedComposeWith A B C F (rightKFlatCompose A C E F S T).obj
        (rightKFlatCompose A C E F S T).property :=
  (derivedBimoduleComposeFunctor A B C F hF).mapIso
      (derivedBimoduleComposeInnerComparisonIso A C E F hF S T q r) ≪≫
    derivedBimoduleComposeKFlatIso A B C F hF (rightKFlatCompose A C E F S T)

lemma derivedBimoduleAssociator_comparison_fac (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) {Q : DerivedBimoduleCategory A C E}
    {R : DerivedBimoduleCategory A E F}
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : Q ≅ (bimoduleToDerived A C E).obj S.obj)
    (r : R ≅ (bimoduleToDerived A E F).obj T.obj) :
    (derivedBimoduleAssociator A B C E F hE hF Q R).hom ≫
        (derivedBimoduleComposeNestedComparisonIso A B C E F hF S T q r).hom =
      (derivedBimoduleComposePairComparisonIso A B C E F hE hF S T q r).hom ≫
        (rightKFlatDerivedAssociator A B C E F S T).hom := by
  have hn := derivedBimoduleAssociator_naturality A B C E F hE hF q.hom r.hom
  have hk := derivedBimoduleAssociatorIso_kFlat_fac A B C E F hE hF S T
  change (derivedBimoduleAssociator A B C E F hE hF _ _).hom ≫ _ = _ at hk
  have hi : (derivedBimoduleComposeInnerComparisonIso A C E F hF S T q r).hom =
      derivedBimoduleComposeInnerMap A C E F hF q.hom r.hom ≫
        (derivedBimoduleComposeKFlatValueIso A C E F hF T S.obj).hom := by
    exact (Category.assoc _ _ _).symm
  change _ ≫ ((derivedBimoduleComposeFunctor A B C F hF).map
      (derivedBimoduleComposeInnerComparisonIso A C E F hF S T q r).hom ≫ _) = _
  rw [hi]
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hn]
  rw [hk]
  simp only [derivedBimoduleComposePairMap, derivedBimoduleComposePairComparisonIso,
    Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    CategoryTheory.Functor.mapIso_hom, Category.assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
