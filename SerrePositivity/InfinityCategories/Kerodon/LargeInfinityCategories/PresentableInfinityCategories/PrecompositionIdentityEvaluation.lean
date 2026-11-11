module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AdjointHomOneFormula

/-!
概要：前合成の単位を恒等関手で評価するための転置の厳密な計算。
方針：二重内部 Hom の評価を各単体で計算し、選んだ随伴の単位公式を保持する。
規約：元の関手・恒等関手・右随伴を単体集合の射として同定する。
使われ方：前合成の単位成分を元の単位へ回収する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

local instance precompositionIdentityHomCategory (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 概要：恒等の関手族の転置を恒等関手で評価すると元の恒等関手。
方針：全単体の評価の成分を計算する。
規約：充填性の仮定は不要。
使われ方：元の単位の始点の回収。 -/
lemma transposeIdentity_evaluate (C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose (𝟙 ((ihom C).obj C)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C)) = 𝟙 C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro c
  change C.map (𝟙 n) c = c
  exact CategoryTheory.Functor.map_id_apply C n c

/-- 概要：前合成の関手族の転置を恒等関手で評価すると元の関手。
方針：全単体の評価の成分を計算する。
規約：元の関手の全単体を保持する。
使われ方：前合成の随伴から元の右随伴を回収する。 -/
lemma transposePre_evaluate {C D : SSet.{u}} (R : D ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose ((pre R).app C) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C)) = R := by
  have h : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose ((pre R).app C) =
      R ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose (𝟙 ((ihom C).obj C)) := by
    simpa only [Category.id_comp] using
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := C) R (𝟙 ((ihom C).obj C)))
  rw [h, Category.assoc, transposeIdentity_evaluate, Category.comp_id]

/-- 概要：前合成の合成族の転置を恒等関手で評価すると元の合成。
方針：前合成の合成則と恒等関手での評価を使う。
規約：左・右関手の元の合成を保持する。
使われ方：前合成の単位の終点の回収。 -/
lemma transposeCompositePre_evaluate {C D : SSet.{u}} (L : C ⟶ D) (R : D ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose ((pre R).app C ≫ (pre L).app C) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C)) = L ≫ R := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposition_composite]
  exact transposePre_evaluate (L ≫ R)

/-- 概要：前合成の全 QCat 随伴の単位を元の Hom 対応で表示する。
方針：自然な Hom 対応からの単位構成の回収式を使う。
規約：指定された同じ前合成の二関手を保持する。
使われ方：元の随伴の単位との比較。 -/
lemma precompositionAdjunction_unitHom {C D Z : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory Z]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionAdjunction (Z := Z) a).unitHom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionTransposeEquiv (Z := Z) a (𝟙 ((ihom C).obj Z)) ((pre R).app Z)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv ((𝟙 ((ihom C).obj Z)) ≫ (pre R).app Z) ((pre R).app Z)
          (Bicategory.leftUnitor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap ((pre R).app Z))).hom) := rfl

/-- 概要：単位の構成へ入力する左単位子の Hom は恒等。
方針：QCat の厳密な左単位子を恒等二胞体へ簡約する。
規約：元の前合成関手の恒等 Hom を保持する。
使われ方：前合成の単位成分の代数的な計算。 -/
lemma precompositionUnitArgument {C D Z : SSet.{u}} [Quasicategory Z] (R : D ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv ((𝟙 ((ihom C).obj Z)) ≫ (pre R).app Z) ((pre R).app Z)
      (Bicategory.leftUnitor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap ((pre R).app Z))).hom =
      𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((pre R).app Z))) := by
  simp only [Bicategory.Strict.leftUnitor_eqToIso, eqToIso.hom, eqToHom_refl]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
