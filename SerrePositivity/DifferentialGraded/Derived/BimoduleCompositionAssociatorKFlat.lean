module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorIndependence

/-! # 全導来結合同型と既存K-flat結合同型の比較図式

## 概要
全導来結合同型と既存K-flat結合同型の比較図式。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionAssociatorComponents.lean、
Derived/BimoduleCompositionTriangle.lean。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
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

lemma derivedBimoduleComposePairResolutionIso_self (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (S : RightKFlatBimoduleCategory A C E)
    (T : RightKFlatBimoduleCategory A E F) :
    derivedBimoduleComposePairResolutionIso A B C E F hE hF S.obj T.obj S T (𝟙 S.obj) (𝟙 T.obj)
        ((BimoduleCategory.quasiIso A C E).id_mem S.obj)
        ((BimoduleCategory.quasiIso A E F).id_mem T.obj) =
      isoWhiskerRight (derivedBimoduleComposeKFlatIso A B C E hE S)
          ((derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj T.obj)) ≪≫
        isoWhiskerLeft (derivedComposeWith A B C E S.obj S.property)
          (derivedBimoduleComposeKFlatIso A B E F hF T) := by
  unfold derivedBimoduleComposePairResolutionIso
  rw [derivedBimoduleComposeResolutionComputation_self,
    derivedBimoduleComposeResolutionComputation_self]

lemma derivedBimoduleComposeInnerResolutionIso_self (hF : localHomKFlat A F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F) :
    derivedBimoduleComposeInnerResolutionIso A C E F hF S.obj T.obj S T (𝟙 S.obj) (𝟙 T.obj)
        ((BimoduleCategory.quasiIso A C E).id_mem S.obj)
        ((BimoduleCategory.quasiIso A E F).id_mem T.obj) =
      derivedBimoduleComposeKFlatValueIso A C E F hF T S.obj := by
  have hi : bimoduleDerivedIso A C E (𝟙 S.obj)
      ((BimoduleCategory.quasiIso A C E).id_mem S.obj) = Iso.refl _ := by
    apply Iso.ext
    exact (bimoduleToDerived A C E).map_id _
  apply Iso.ext
  change (derivedBimoduleComposeResolutionComputation A C E F hF T.obj T (𝟙 T.obj)
      ((BimoduleCategory.quasiIso A E F).id_mem T.obj)).hom.app
        ((bimoduleToDerived A C E).obj S.obj) ≫
      (derivedComposeWith A C E F T.obj T.property).map
        (bimoduleDerivedIso A C E (𝟙 S.obj)
          ((BimoduleCategory.quasiIso A C E).id_mem S.obj)).inv = _
  rw [hi, Iso.refl_inv, derivedBimoduleComposeResolutionComputation_self,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

lemma derivedBimoduleComposeNestedResolutionIso_self (hF : localHomKFlat A F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F) :
    derivedBimoduleComposeNestedResolutionIso A B C E F hF S.obj T.obj S T (𝟙 S.obj) (𝟙 T.obj)
        ((BimoduleCategory.quasiIso A C E).id_mem S.obj)
        ((BimoduleCategory.quasiIso A E F).id_mem T.obj) =
      (derivedBimoduleComposeFunctor A B C F hF).mapIso
          (derivedBimoduleComposeKFlatValueIso A C E F hF T S.obj) ≪≫
        derivedBimoduleComposeKFlatIso A B C F hF (rightKFlatCompose A C E F S T) := by
  unfold derivedBimoduleComposeNestedResolutionIso
  rw [derivedBimoduleComposeInnerResolutionIso_self]

lemma derivedBimoduleAssociatorIso_kFlat_fac (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (S : RightKFlatBimoduleCategory A C E)
    (T : RightKFlatBimoduleCategory A E F) :
    (((derivedBimoduleAssociatorIso A B C E F hE hF).app
        ((bimoduleToDerived A E F).obj T.obj)).app ((bimoduleToDerived A C E).obj S.obj)).hom ≫
      ((derivedBimoduleComposeFunctor A B C F hF).map
          (derivedBimoduleComposeKFlatValueIso A C E F hF T S.obj).hom ≫
        (derivedBimoduleComposeKFlatIso A B C F hF (rightKFlatCompose A C E F S T)).hom) =
    (whiskerRight (derivedBimoduleComposeKFlatIso A B C E hE S).hom
        ((derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj T.obj)) ≫
      whiskerLeft (derivedComposeWith A B C E S.obj S.property)
        (derivedBimoduleComposeKFlatIso A B E F hF T).hom) ≫
      (rightKFlatDerivedAssociator A B C E F S T).hom := by
  have h := derivedBimoduleAssociatorIso_resolution_fac A B C E F hE hF S.obj T.obj S T
    (𝟙 S.obj) (𝟙 T.obj) ((BimoduleCategory.quasiIso A C E).id_mem S.obj)
    ((BimoduleCategory.quasiIso A E F).id_mem T.obj)
  rw [derivedBimoduleComposePairResolutionIso_self,
    derivedBimoduleComposeNestedResolutionIso_self] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
