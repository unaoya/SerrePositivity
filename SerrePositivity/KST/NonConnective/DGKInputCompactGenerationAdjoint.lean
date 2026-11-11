module
public import SerrePositivity.KST.NonConnective.DGKInputCompactNativeComposition
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-!
概要：同じ compact 生成同値の順逆射と単位を保ち、三角恒等式を持つ比較へ正規化する。
方針：Mathlib の quasicategory の厳密二圏と既存の余単位正規化を直接使う。
規約：固定 ν と同じ生成射を保持し、存在仮定を追加しない。全高次整合は別工程。
使われ方：K-7 d4 の恒等作用と二項合成比較の整合を検証する実データ。
-/

@[expose] public section
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
noncomputable section
universe u v
namespace SerrePositivity.KST.NonConnective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (A : PerfDGInput.{u, v} R)
/-- 概要：同じ固定 ν 値の宇宙移送を、quasicategory 二圏の実始域にする。
方針：元の単体集合と既存の quasicategory 性を束ねる。
規約：元の固定 ν 値を変更しない。
使われ方：同じ生成射の二圏表示。 -/
def dgKInputCompactGenerationSourceQCat : SSet.QCat.{max (u + 1) v + 1} :=
  ⟨(SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
    (dgKInputStableValue R A).obj, inferInstance⟩
/-- 概要：同じ Indω の compact 生成元を、quasicategory 二圏の実標的にする。
方針：元の compact 部分単体集合をそのまま束ねる。
規約：非可算 κ の cone と同一視しない。
使われ方：同じ生成射の二圏表示。 -/
def dgKInputCompactGenerationTargetQCat : SSet.QCat.{max (u + 1) v + 1} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{max (u + 1) v, max (u + 1) v + 1}
    Cardinal.aleph0 (dgKInputIndCompletion R A), inferInstance⟩
/-- 概要：元の compact 生成順射を二圏の一射にする。
方針：元の単体集合の射を充満部分圏の射に包む。
規約：底の射を選び直さない。
使われ方：元の compact Yoneda の厳密回収。 -/
def dgKInputCompactGenerationBicategoricalHom :
    dgKInputCompactGenerationSourceQCat R A ⟶ dgKInputCompactGenerationTargetQCat R A :=
  ObjectProperty.homMk (dgKInputCompactGenerationEquivalence R A).hom
/-- 概要：元の compact 生成逆射を二圏の一射にする。
方針：元の指定逆射を充満部分圏の射に包む。
規約：元の逆射を保持する。
使われ方：生成比較の正規化。 -/
def dgKInputCompactGenerationBicategoricalInv :
    dgKInputCompactGenerationTargetQCat R A ⟶ dgKInputCompactGenerationSourceQCat R A :=
  ObjectProperty.homMk (dgKInputCompactGenerationEquivalence R A).inv
/-- 概要：元の生成単位を二圏の可逆二射として保持する。
方針：元の homInvIso の逆を既存の Hom.mk に渡す。
規約：同じ全関手同型を使う。
使われ方：単位を変えない余単位正規化。 -/
def dgKInputCompactGenerationBicategoricalUnit :
    𝟙 (dgKInputCompactGenerationSourceQCat R A) ≅
      dgKInputCompactGenerationBicategoricalHom R A ≫
        dgKInputCompactGenerationBicategoricalInv R A where
  hom := CatEnrichedOrdinary.Hom.mk (dgKInputCompactGenerationEquivalence R A).homInvIso.inv
  inv := CatEnrichedOrdinary.Hom.mk (dgKInputCompactGenerationEquivalence R A).homInvIso.hom
  hom_inv_id := by
    apply CatEnrichedOrdinary.Hom.ext
    exact (dgKInputCompactGenerationEquivalence R A).homInvIso.inv_hom_id
  inv_hom_id := by
    apply CatEnrichedOrdinary.Hom.ext
    exact (dgKInputCompactGenerationEquivalence R A).homInvIso.hom_inv_id
/-- 概要：元の生成余単位を二圏の可逆二射として読む。
方針：元の invHomIso を既存の Hom.mk に渡す。
規約：三角恒等式をここでは主張しない。
使われ方：正規化前の実入力。 -/
def dgKInputCompactGenerationBicategoricalCounit :
    dgKInputCompactGenerationBicategoricalInv R A ≫
      dgKInputCompactGenerationBicategoricalHom R A ≅
        𝟙 (dgKInputCompactGenerationTargetQCat R A) where
  hom := CatEnrichedOrdinary.Hom.mk (dgKInputCompactGenerationEquivalence R A).invHomIso.hom
  inv := CatEnrichedOrdinary.Hom.mk (dgKInputCompactGenerationEquivalence R A).invHomIso.inv
  hom_inv_id := by
    apply CatEnrichedOrdinary.Hom.ext
    exact (dgKInputCompactGenerationEquivalence R A).invHomIso.hom_inv_id
  inv_hom_id := by
    apply CatEnrichedOrdinary.Hom.ext
    exact (dgKInputCompactGenerationEquivalence R A).invHomIso.inv_hom_id
/-- 概要：同じ生成順逆射と単位を保つ随伴同値を構成する。
方針：正本の mkOfAdjointifyCounit に元の可逆二射を渡す。
規約：余単位だけを正規化し、新たな存在入力を要求しない。
使われ方：K-7 d4 の二つの三角恒等式。 -/
def dgKInputCompactGenerationAdjointEquivalence :
    Bicategory.Equivalence (dgKInputCompactGenerationSourceQCat R A)
      (dgKInputCompactGenerationTargetQCat R A) :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (dgKInputCompactGenerationBicategoricalUnit R A)
    (dgKInputCompactGenerationBicategoricalCounit R A)
/-- 概要：正規化した同じ生成比較の余単位を全関手同型として回収する。
方針：二圏の二射の元の関手空間表示を使う。
規約：順射・逆射は元の生成同値のまま。
使われ方：恒等作用と二項合成比較の整合。 -/
def dgKInputCompactGenerationAdjointCounit : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgKInputCompactGenerationEquivalence R A).inv ≫
      (dgKInputCompactGenerationEquivalence R A).hom) (𝟙 _) where
  hom := CatEnrichedOrdinary.Hom.base (dgKInputCompactGenerationAdjointEquivalence R A).counit.hom
  inv := CatEnrichedOrdinary.Hom.base (dgKInputCompactGenerationAdjointEquivalence R A).counit.inv
  hom_inv_id := congrArg CatEnrichedOrdinary.Hom.base
    (dgKInputCompactGenerationAdjointEquivalence R A).counit.hom_inv_id
  inv_hom_id := congrArg CatEnrichedOrdinary.Hom.base
    (dgKInputCompactGenerationAdjointEquivalence R A).counit.inv_hom_id

/-- 概要：随伴正規化の順射は元の compact Yoneda を表す同じ実射。
方針：正規化の順射の定義を展開する。
規約：順射を同型で置き換えない。
使われ方：K-7 d4 の元の生成同値との厳密照合。 -/
theorem dgKInputCompactGenerationAdjointEquivalence_hom :
    (dgKInputCompactGenerationAdjointEquivalence R A).hom.hom =
      (dgKInputCompactGenerationEquivalence R A).hom := rfl

/-- 概要：随伴正規化の逆射も元の指定生成逆射そのもの。
方針：正規化の逆射の定義を展開する。
規約：別の逆射選択を導入しない。
使われ方：既存の全 native 作用との厳密照合。 -/
theorem dgKInputCompactGenerationAdjointEquivalence_inv :
    (dgKInputCompactGenerationAdjointEquivalence R A).inv.hom =
      (dgKInputCompactGenerationEquivalence R A).inv := rfl

/-- 概要：正規化後も元の全生成単位を保つ。
方針：余単位正規化の元の単位を展開する。
規約：元の二項合成比較の単位を変更しない。
使われ方：既存の全 native 合成比較への接続。 -/
theorem dgKInputCompactGenerationAdjointEquivalence_unit :
    (dgKInputCompactGenerationAdjointEquivalence R A).unit =
      dgKInputCompactGenerationBicategoricalUnit R A := rfl

/-- 概要：同じ生成順射上で、元の単位と正規化余単位は左三角恒等式を満たす。
方針：Mathlib の随伴同値が保持する左三角式を特殊化する。
規約：同じ実二射を保持し、全高次整合をこの等式から推論しない。
使われ方：K-7 d4 の恒等・二項合成の二圏的整合。 -/
theorem dgKInputCompactGenerationAdjointEquivalence_left_triangle :
    Bicategory.leftZigzagIso (dgKInputCompactGenerationAdjointEquivalence R A).unit
        (dgKInputCompactGenerationAdjointEquivalence R A).counit =
      (Bicategory.leftUnitor (dgKInputCompactGenerationAdjointEquivalence R A).hom) ≪≫
        (Bicategory.rightUnitor (dgKInputCompactGenerationAdjointEquivalence R A).hom).symm :=
  (dgKInputCompactGenerationAdjointEquivalence R A).left_triangle

/-- 概要：同じ生成逆射上でも元の単位と正規化余単位は右三角恒等式を満たす。
方針：Mathlib の随伴同値の右三角式を特殊化する。
規約：元の指定逆射を変えず、全高次整合は別工程に保持する。
使われ方：K-7 d4 の逆射側の恒等・二項合成の整合。 -/
theorem dgKInputCompactGenerationAdjointEquivalence_right_triangle :
    Bicategory.rightZigzagIso (dgKInputCompactGenerationAdjointEquivalence R A).unit
        (dgKInputCompactGenerationAdjointEquivalence R A).counit =
      (Bicategory.rightUnitor (dgKInputCompactGenerationAdjointEquivalence R A).inv) ≪≫
        (Bicategory.leftUnitor (dgKInputCompactGenerationAdjointEquivalence R A).inv).symm :=
  (dgKInputCompactGenerationAdjointEquivalence R A).right_triangle

/-- 概要：元の恒等 dg 射の compact 作用を、三角恒等式を持つ同じ生成余単位で比較する。
方針：固定 ν の恒等保存を厳密に回収し、正規化した生成余単位を使う。
規約：元の作用射・生成順逆射・二項合成の単位を変更せず、既存の恒等比較も保持する。
使われ方：K-7 d4 の恒等作用と二項合成比較の二圏的整合。 -/
def dgKInputCompactNativeMap_adjointIdIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKInputCompactNativeMap R A A (𝟙 A)) (𝟙 _) := by
  have hν : (dgKInputNuMap R (𝟙 A)).hom = 𝟙 (dgKInputStableValue R A).obj := by
    rw [dgKInputNuMap_eq]
    exact congrArg (fun f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
      (dgKInputStableValue R A) (dgKInputStableValue R A) => f.hom)
      ((presentedPerfectDGStableCategoryFunctor R).map_id A)
  unfold dgKInputCompactNativeMap
  rw [hν, CategoryTheory.Functor.map_id, Category.id_comp]
  exact dgKInputCompactGenerationAdjointCounit R A

end SerrePositivity.KST.NonConnective
