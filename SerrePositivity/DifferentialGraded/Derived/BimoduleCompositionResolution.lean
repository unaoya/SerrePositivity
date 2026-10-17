module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposition

/-! # 全導来合成の解像度計算同型と増大射・比較squareの整合性

## 概要
全導来合成の解像度計算同型と増大射・比較squareの整合性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPairResolution.lean、
Derived/BimoduleCompositionResolutionValues.lean、Derived/BimoduleCompositionRightUnit.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

lemma derivedBimoduleComposeResolutionComputation_fac (hE : localHomKFlat A E)
    (Q : BimoduleCategory A C E) (R : RightKFlatBimoduleCategory A C E)
    (q : R.obj ⟶ Q) (hq : BimoduleCategory.quasiIso A C E q) :
    (derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map q) ≫
        (derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).hom =
      (derivedBimoduleComposeKFlatIso A B C E hE R).hom := by
  change (derivedBimoduleComposeFunctor A B C E hE).map
      (bimoduleDerivedIso A C E q hq).hom ≫
    ((derivedBimoduleComposeFunctor A B C E hE).map
      (bimoduleDerivedIso A C E q hq).inv ≫ _) = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

lemma derivedBimoduleComposeResolutionComputation_self (hE : localHomKFlat A E)
    (R : RightKFlatBimoduleCategory A C E) :
    derivedBimoduleComposeResolutionComputation A B C E hE R.obj R (𝟙 R.obj)
        ((BimoduleCategory.quasiIso A C E).id_mem R.obj) =
      derivedBimoduleComposeKFlatIso A B C E hE R := by
  apply Iso.ext
  have h := derivedBimoduleComposeResolutionComputation_fac A B C E hE R.obj R (𝟙 R.obj)
    ((BimoduleCategory.quasiIso A C E).id_mem R.obj)
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using h

/-- 増大squareは導来圏で可換ならよく、閉零圏での厳密な可換性を要求しない。 -/
lemma derivedBimoduleComposeResolutionComputation_naturality (hE : localHomKFlat A E)
    {Q Q' : BimoduleCategory A C E} (R S : RightKFlatBimoduleCategory A C E)
    (q : R.obj ⟶ Q) (r : S.obj ⟶ Q')
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A C E r)
    (f : Q ⟶ Q') (g : R ⟶ S)
    (h : (bimoduleToDerived A C E).map q ≫ (bimoduleToDerived A C E).map f =
      (bimoduleToDerived A C E).map g.hom ≫ (bimoduleToDerived A C E).map r) :
    (derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map f) ≫
        (derivedBimoduleComposeResolutionComputation A B C E hE Q' S r hr).hom =
      (derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).hom ≫
        derivedComposeWithMap A B C E R.property S.property g.hom := by
  apply (Iso.cancel_iso_hom_left
    ((derivedBimoduleComposeFunctor A B C E hE).mapIso (bimoduleDerivedIso A C E q hq)) _ _).1
  change (derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map q) ≫
      ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map f) ≫
        (derivedBimoduleComposeResolutionComputation A B C E hE Q' S r hr).hom) =
    (derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map q) ≫
      ((derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).hom ≫
        derivedComposeWithMap A B C E R.property S.property g.hom)
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, h,
    CategoryTheory.Functor.map_comp, Category.assoc,
    derivedBimoduleComposeResolutionComputation_fac]
  rw [← Category.assoc, derivedBimoduleComposeResolutionComputation_fac]
  exact derivedBimoduleComposeKFlatIso_naturality A B C E hE g

end SerrePositivity.DifferentialGraded.BimoduleTensor
