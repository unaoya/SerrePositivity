module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorAssociator
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorUnit

/-! # 標準局所化の元の対象・射上での導来合成の計算

## 概要
標準局所化の元の対象・射上での導来合成の計算。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionRightUnit.lean、Derived/
BimoduleCompositionValueNaturality.lean、Derived/BimoduleTensorNaturality.lean等。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma derivedComposeWith_map_base (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    {P P' : BimoduleCategory A B C} (f : P ⟶ P') :
    (derivedComposeWith A B C E Q hQ).map ((bimoduleToDerived A B C).map f) =
      (bimoduleToDerived A B E).map (composeMap A B C E f (𝟙 Q)) := rfl

lemma derivedComposeWithMap_base_app {Q Q' : BimoduleCategory A C E}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (g : Q ⟶ Q') (P : BimoduleCategory A B C) :
    (derivedComposeWithMap A B C E hQ hQ' g).app ((bimoduleToDerived A B C).obj P) =
      (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) g) := by
  have h := derivedComposeWithMap_app A B C E hQ hQ' g P
  change (derivedComposeWithMap A B C E hQ hQ' g).app ((bimoduleToDerived A B C).obj P) =
    𝟙 _ ≫ (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) g) ≫ 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id] using h

lemma derivedRightUnitIso_base_app (P : BimoduleCategory A B C) :
    (derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P) =
      (bimoduleToDerived A B C).map
        (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom := by
  have h := derivedRightUnitIso_hom_app A B C P
  change (derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P) =
    𝟙 _ ≫ (bimoduleToDerived A B C).map
      (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom at h
  exact h.trans (Category.id_comp _)

variable (F : Type t) [DGCategory A F] [Small.{u} E]

lemma derivedAssociatorIso_base_app (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hR : Bimodule.rightRelativeKFlat A E F (BimoduleCategory.underlying A E F R))
    (P : BimoduleCategory A B C) :
    (derivedAssociatorIso A B C E F Q R hQ hR).hom.app ((bimoduleToDerived A B C).obj P) =
      (bimoduleToDerived A B F).map
        (associatorIso A B C E F (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)).hom := by
  have h := derivedAssociatorIso_hom_app A B C E F Q R hQ hR P
  change (derivedAssociatorIso A B C E F Q R hQ hR).hom.app
      ((bimoduleToDerived A B C).obj P) = 𝟙 _ ≫ (bimoduleToDerived A B F).map
        (associatorIso A B C E F (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)).hom ≫ 𝟙 _
      at h
  simpa only [Category.id_comp, Category.comp_id] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
