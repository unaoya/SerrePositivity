module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.Triangle

/-! # 固定した右相対K-flat因子に関する導来合成の三角coherence

## 概要
固定した右相対K-flat因子に関する導来合成の三角coherence。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionTriangle.lean。
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
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma derivedTriangle (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    (derivedAssociatorIso A B C C E
        (BimoduleCategory.of A C C (Bimodule.diagonal A C)) Q
        (Bimodule.diagonal_rightRelativeKFlat A C) hQ).hom ≫
      derivedComposeWithMap A B C E
        (Bimodule.rightRelativeKFlat_compose A C C E (Bimodule.diagonal A C)
          (BimoduleCategory.underlying A C E Q) (Bimodule.diagonal_rightRelativeKFlat A C) hQ)
        hQ (leftBimoduleUnitIso A C E (BimoduleCategory.underlying A C E Q)).hom =
    whiskerRight (derivedRightUnitIso A B C).hom (derivedComposeWith A B C E Q hQ) ≫
      (Functor.leftUnitor (derivedComposeWith A B C E Q hQ)).hom := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  simp only [NatTrans.comp_app, whiskerRight_app, Functor.leftUnitor_hom_app,
    derivedAssociatorIso_base_app, derivedComposeWithMap_base_app,
    derivedRightUnitIso_base_app, derivedComposeWith_map_base]
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun f => (bimoduleToDerived A B E).map f)
    (triangle A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
