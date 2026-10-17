module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposeHomotopy
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparison

/-! # ホモトピー可換な増大squareに対する中間圏比較の計算射の整合性

## 概要
ホモトピー可換な増大squareに対する中間圏比較の計算射の整合性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)

/-- 増大射をsourceの全dg自然なホモトピーで替えても、比較の計算射の導来像は変わらない。 -/
lemma middleRestrictionResolvedMap_eq_of_source_homotopy
    (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A D E)
    (q q' : R ⟶ BimoduleCategory.of A D E
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q)))
    (h : (moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A D E).inverse.map q) =
      (moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A D E).inverse.map q')) :
    (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q R q) =
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q R q') := by
  have he := composeAfter_map_eq_of_inverse_source_homotopy A B D E
    (BimoduleCategory.of A B D
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P))) q q' h
  dsimp only [middleRestrictionResolvedMap]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  exact congrArg (fun k => k ≫ (bimoduleToDerived A B E).map
    (middleRestrictionComparisonMap A B C D E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q))) he

/-- 解像度比較の増大squareはsourceの主Kで可換なら十分である。 -/
lemma middleRestrictionResolvedMap_comp_of_source_homotopy
    (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
    {R S : BimoduleCategory A D E}
    (q : R ⟶ BimoduleCategory.of A D E
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q)))
    (s : S ⟶ BimoduleCategory.of A D E
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q))) (r : R ⟶ S)
    (h : (moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A D E).inverse.map (r ≫ s)) =
      (moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A D E).inverse.map q)) :
    (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) r) ≫
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q S s) =
    (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q R q) := by
  rw [← CategoryTheory.Functor.map_comp, middleRestrictionResolvedMap_comp]
  exact middleRestrictionResolvedMap_eq_of_source_homotopy A B C D E F P Q R (r ≫ s) q h

end SerrePositivity.DifferentialGraded.BimoduleTensor
