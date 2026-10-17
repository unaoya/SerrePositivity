module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPairResolution

/-! # 二つの解像度比較squareに関する逐次導来合成の自然性

## 概要
二つの解像度比較squareに関する逐次導来合成の自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionInnerNaturality.lean。
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

def derivedBimoduleComposePairMap (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    {Q Q' : DerivedBimoduleCategory A C E} {R R' : DerivedBimoduleCategory A E F}
    (f : Q ⟶ Q') (g : R ⟶ R') :
    (derivedBimoduleComposeFunctor A B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R ⟶
      (derivedBimoduleComposeFunctor A B C E hE).obj Q' ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R' :=
  whiskerRight ((derivedBimoduleComposeFunctor A B C E hE).map f)
      ((derivedBimoduleComposeFunctor A B E F hF).obj R) ≫
    whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj Q')
      ((derivedBimoduleComposeFunctor A B E F hF).map g)

lemma derivedBimoduleComposePairResolutionIso_naturality
    (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    {Q Q' : BimoduleCategory A C E} {R R' : BimoduleCategory A E F}
    (S S' : RightKFlatBimoduleCategory A C E) (T T' : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (q' : S'.obj ⟶ Q') (r : T.obj ⟶ R) (r' : T'.obj ⟶ R')
    (hq : BimoduleCategory.quasiIso A C E q) (hq' : BimoduleCategory.quasiIso A C E q')
    (hr : BimoduleCategory.quasiIso A E F r) (hr' : BimoduleCategory.quasiIso A E F r')
    (f : Q ⟶ Q') (g : R ⟶ R') (s : S ⟶ S') (t : T ⟶ T')
    (hs : (bimoduleToDerived A C E).map q ≫ (bimoduleToDerived A C E).map f =
      (bimoduleToDerived A C E).map s.hom ≫ (bimoduleToDerived A C E).map q')
    (ht : (bimoduleToDerived A E F).map r ≫ (bimoduleToDerived A E F).map g =
      (bimoduleToDerived A E F).map t.hom ≫ (bimoduleToDerived A E F).map r') :
    derivedBimoduleComposePairMap A B C E F hE hF
        ((bimoduleToDerived A C E).map f) ((bimoduleToDerived A E F).map g) ≫
      (derivedBimoduleComposePairResolutionIso A B C E F hE hF Q' R' S' T' q' r' hq' hr').hom =
    (derivedBimoduleComposePairResolutionIso A B C E F hE hF Q R S T q r hq hr).hom ≫
      (whiskerRight (derivedComposeWithMap A B C E S.property S'.property s.hom)
          (derivedComposeWith A B E F T.obj T.property) ≫
        whiskerLeft (derivedComposeWith A B C E S'.obj S'.property)
          (derivedComposeWithMap A B E F T.property T'.property t.hom)) := by
  have hqnat := derivedBimoduleComposeResolutionComputation_naturality
    A B C E hE S S' q q' hq hq' f s hs
  have hrnat := derivedBimoduleComposeResolutionComputation_naturality
    A B E F hF T T' r r' hr hr' g t ht
  ext P
  have hqP := NatTrans.congr_app hqnat P
  have hrP := NatTrans.congr_app hrnat
    ((derivedComposeWith A B C E S'.obj S'.property).obj P)
  simp only [NatTrans.comp_app] at hqP hrP
  have hx := ((derivedBimoduleComposeFunctor A B E F hF).map
    ((bimoduleToDerived A E F).map g)).naturality
      ((derivedBimoduleComposeResolutionComputation A B C E hE Q' S' q' hq').hom.app P)
  have hy := (derivedBimoduleComposeResolutionComputation A B E F hF R T r hr).hom.naturality
    ((derivedComposeWithMap A B C E S.property S'.property s.hom).app P)
  change (_ ≫ _) ≫ (_ ≫ _) = (_ ≫ _) ≫ (_ ≫ _)
  simp only [isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    Category.assoc]
  rw [← reassoc_of% hx]
  simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [hqP, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [hrP]
  rw [reassoc_of% hy]

end SerrePositivity.DifferentialGraded.BimoduleTensor
