module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionResolutionValues
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorEvaluation

/-! # 導来合成の値の指定解像度計算と後因子の射の整合性

## 概要
導来合成の値の指定解像度計算と後因子の射の整合性。

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
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]

lemma derivedBimoduleComposeResolutionValueIso_naturality (hE : localHomKFlat A E)
    {Q Q' : BimoduleCategory A C E} (R S : RightKFlatBimoduleCategory A C E)
    (q : R.obj ⟶ Q) (s : S.obj ⟶ Q')
    (hq : BimoduleCategory.quasiIso A C E q) (hs : BimoduleCategory.quasiIso A C E s)
    (f : Q ⟶ Q') (r : R ⟶ S)
    (h : (bimoduleToDerived A C E).map q ≫ (bimoduleToDerived A C E).map f =
      (bimoduleToDerived A C E).map r.hom ≫ (bimoduleToDerived A C E).map s)
    (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map f)).app
        ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleComposeResolutionValueIso A B C E hE Q' S s hs P).hom =
    (derivedBimoduleComposeResolutionValueIso A B C E hE Q R q hq P).hom ≫
      (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) r.hom) := by
  have hn := NatTrans.congr_app
    (derivedBimoduleComposeResolutionComputation_naturality A B C E hE R S q s hq hs f r h)
    ((bimoduleToDerived A B C).obj P)
  simp only [NatTrans.comp_app] at hn
  dsimp only [derivedBimoduleComposeResolutionValueIso, Iso.trans_hom]
  simp only [Iso.app_hom]
  rw [← Category.assoc, hn, Category.assoc, derivedComposeWithMap_computation, ← Category.assoc]

lemma derivedBimoduleComposeKFlatValueIso_naturality (hE : localHomKFlat A E)
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom)).app
        ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleComposeKFlatValueIso A B C E hE Q' P).hom =
    (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom ≫
      (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) g.hom) := by
  have h := NatTrans.congr_app (derivedBimoduleComposeKFlatIso_naturality A B C E hE g)
    ((bimoduleToDerived A B C).obj P)
  simp only [NatTrans.comp_app, derivedComposeWithMap_base_app] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
