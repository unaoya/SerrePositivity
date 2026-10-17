module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorKFlat

/-! # 全導来結合同型の成分と二つの後因子に関する同時自然性

## 概要
全導来結合同型の成分と二つの後因子に関する同時自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionAssociatorComparison.lean。
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

/-- 任意の二つの導来後因子で評価した、前因子全体に自然な結合同型。 -/
def derivedBimoduleAssociator (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E F) :
    (derivedBimoduleComposeFunctor A B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R ≅
      (derivedBimoduleComposeFunctor A B C F hF).obj
        (((derivedBimoduleComposeFunctor A C E F hF).obj R).obj Q) :=
  ((derivedBimoduleAssociatorIso A B C E F hE hF).app R).app Q

lemma derivedBimoduleAssociator_naturality (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) {Q Q' : DerivedBimoduleCategory A C E}
    {R R' : DerivedBimoduleCategory A E F} (f : Q ⟶ Q') (g : R ⟶ R') :
    derivedBimoduleComposePairMap A B C E F hE hF f g ≫
        (derivedBimoduleAssociator A B C E F hE hF Q' R').hom =
      (derivedBimoduleAssociator A B C E F hE hF Q R).hom ≫
        (derivedBimoduleComposeFunctor A B C F hF).map
          (derivedBimoduleComposeInnerMap A C E F hF f g) := by
  have hQ := ((derivedBimoduleAssociatorIso A B C E F hE hF).hom.app R).naturality f
  have hR := NatTrans.congr_app
    ((derivedBimoduleAssociatorIso A B C E F hE hF).hom.naturality g) Q'
  change whiskerRight ((derivedBimoduleComposeFunctor A B C E hE).map f)
      ((derivedBimoduleComposeFunctor A B E F hF).obj R) ≫
      (derivedBimoduleAssociator A B C E F hE hF Q' R).hom =
    (derivedBimoduleAssociator A B C E F hE hF Q R).hom ≫
      (derivedBimoduleComposeFunctor A B C F hF).map
        (((derivedBimoduleComposeFunctor A C E F hF).obj R).map f) at hQ
  change whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj Q')
      ((derivedBimoduleComposeFunctor A B E F hF).map g) ≫
      (derivedBimoduleAssociator A B C E F hE hF Q' R').hom =
    (derivedBimoduleAssociator A B C E F hE hF Q' R).hom ≫
      (derivedBimoduleComposeFunctor A B C F hF).map
        (((derivedBimoduleComposeFunctor A C E F hF).map g).app Q') at hR
  change (_ ≫ _) ≫ _ = _ ≫ (derivedBimoduleComposeFunctor A B C F hF).map (_ ≫ _)
  rw [Category.assoc, hR, ← Category.assoc, hQ, Category.assoc,
    ← CategoryTheory.Functor.map_comp]

end SerrePositivity.DifferentialGraded.BimoduleTensor
