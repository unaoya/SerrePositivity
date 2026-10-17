module
public import SerrePositivity.DifferentialGraded.Derived.RightKFlatComposition
public import SerrePositivity.DifferentialGraded.Tensor.Pentagon

/-! # 三つの固定右K-flat因子に関する導来合成の五角coherence

## 概要
三つの固定右K-flat因子に関する導来合成の五角coherence。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPentagonInner.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t x
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

lemma derivedPentagon (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A E F) (S : RightKFlatBimoduleCategory A F G) :
    whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (rightKFlatDerivedAssociator A B E F G R S).hom ≫
      (rightKFlatDerivedAssociator A B C E G Q (rightKFlatCompose A E F G R S)).hom =
    whiskerRight (rightKFlatDerivedAssociator A B C E F Q R).hom
        (rightKFlatDerivedCompose A B F G S) ≫
      (rightKFlatDerivedAssociator A B C F G (rightKFlatCompose A C E F Q R) S).hom ≫
      rightKFlatDerivedMap A B C G
        (Q := rightKFlatCompose A C F G (rightKFlatCompose A C E F Q R) S)
        (Q' := rightKFlatCompose A C E G Q (rightKFlatCompose A E F G R S))
        (associatorIso A C E F G (BimoduleCategory.underlying A C E Q.obj)
          (BimoduleCategory.underlying A E F R.obj) (BimoduleCategory.underlying A F G S.obj)).hom
      := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    rightKFlatDerivedAssociator_base_app]
  have hm : (rightKFlatDerivedAssociator A B E F G R S).hom.app
      ((rightKFlatDerivedCompose A B C E Q).obj ((bimoduleToDerived A B C).obj P)) =
      (bimoduleToDerived A B G).map
        (associatorIso A B E F G
          (compose A B C E (BimoduleCategory.underlying A B C P)
            (BimoduleCategory.underlying A C E Q.obj))
          (BimoduleCategory.underlying A E F R.obj) (BimoduleCategory.underlying A F G S.obj)).hom
      :=
    rightKFlatDerivedAssociator_base_app A B E F G R S
      (BimoduleCategory.of A B E (compose A B C E
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q.obj)))
  rw [hm]
  simp only [rightKFlatDerivedCompose, rightKFlatDerivedMap,
    derivedComposeWith_map_base, derivedComposeWithMap_base_app,
    ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun f => (bimoduleToDerived A B G).map f)
    (pentagon A B C E F G (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q.obj) (BimoduleCategory.underlying A E F R.obj)
      (BimoduleCategory.underlying A F G S.obj))

end SerrePositivity.DifferentialGraded.BimoduleTensor
