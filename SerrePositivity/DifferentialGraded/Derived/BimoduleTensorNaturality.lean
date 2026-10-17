module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorEvaluation

/-! # 固定因子の二つの射に関する導来結合比較の自然性

## 概要
固定因子の二つの射に関する導来結合比較の自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionAssociatorNaturality.lean。
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
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

lemma derivedAssociatorIso_naturality {Q Q' : BimoduleCategory A C E}
    {R R' : BimoduleCategory A E F}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (hR : Bimodule.rightRelativeKFlat A E F (BimoduleCategory.underlying A E F R))
    (hR' : Bimodule.rightRelativeKFlat A E F (BimoduleCategory.underlying A E F R'))
    (g : Q ⟶ Q') (h : R ⟶ R') :
    (whiskerRight (derivedComposeWithMap A B C E hQ hQ' g) (derivedComposeWith A B E F R hR) ≫
        whiskerLeft (derivedComposeWith A B C E Q' hQ')
          (derivedComposeWithMap A B E F hR hR' h)) ≫
      (derivedAssociatorIso A B C E F Q' R' hQ' hR').hom =
    (derivedAssociatorIso A B C E F Q R hQ hR).hom ≫
      derivedComposeWithMap A B C F
        (Bimodule.rightRelativeKFlat_compose A C E F
          (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R) hQ hR)
        (Bimodule.rightRelativeKFlat_compose A C E F
          (BimoduleCategory.underlying A C E Q') (BimoduleCategory.underlying A E F R') hQ' hR')
        (composeMap A C E F g h) := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    derivedComposeWithMap_base_app, derivedComposeWith_map_base, derivedAssociatorIso_base_app]
  have hm : (derivedComposeWithMap A B E F hR hR' h).app
      ((derivedComposeWith A B C E Q' hQ').obj ((bimoduleToDerived A B C).obj P)) =
      (bimoduleToDerived A B F).map (composeMap A B E F
        (𝟙 (BimoduleCategory.of A B E (compose A B C E
          (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q')))) h) :=
    derivedComposeWithMap_base_app A B E F hR hR' h
      (BimoduleCategory.of A B E (compose A B C E
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q')))
  rw [hm]
  simp only [← CategoryTheory.Functor.map_comp]
  have hc := composeMap_comp A B E F (composeMap A B C E (𝟙 P) g)
    (𝟙 (BimoduleCategory.of A B E (compose A B C E
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q')))) (𝟙 R) h
  simp only [Category.comp_id, Category.id_comp] at hc
  have hn := associatorIso_naturality A B C E F (𝟙 P) g h
  rw [hc] at hn
  exact congrArg (fun f => (bimoduleToDerived A B F).map f) hn

end SerrePositivity.DifferentialGraded.BimoduleTensor
