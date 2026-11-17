module

public import SerrePositivity.EInfinity.Modules.RelativeLocalizationEquivalence
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# 同じ相対局所化の自然変換を回収するための円筒の法則

概要：HA §1.3.4 の同じ弱自然変換の比較を、通常の関手の円筒で計算する。
方針：区間との積の指定弱射を元の圏への射影で検出する。
規約：既存の局所化関手の自然性の証明の分割であり、モデル構造を要求しない。
使われ方：同じ BE 底の模型の単位・余単位を全関手圏に回収する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

variable (C : RelativeCategory.{u})

/-- 概要：同じ相対関手の円筒の指定弱射（HA §1.3.4）。
方針：区間との積の弱射を射影の逆像に取る。
規約：元の圏の弱射を変更しない。使われ方：弱自然変換の計算。 -/
def relativeCylinder : RelativeCategory.{u} where
  category := Cat.of (Fin 2 × C.category)
  weakEquivalences := C.weakEquivalences.inverseImage (CategoryTheory.Prod.snd (Fin 2) C.category)
  isMultiplicative := inferInstance

/-- 概要：同じ円筒の射影は相対関手（HA §1.3.4）。
方針：指定弱射の定義を使う。
規約：通常の積の射影。使われ方：局所化後の円筒の比較。 -/
def relativeCylinderProjection : relativeCylinder C ⟶ C where
  functor := CategoryTheory.Prod.snd (Fin 2) C.category
  map := fun _ _ _ hf => hf

/-- 概要：同じ円筒の端点は相対関手（HA §1.3.4）。
方針：元の射を区間上の恒等射と組にする。
規約：同じ両端点。使われ方：自然変換の両側の回収。 -/
def relativeCylinderEndpoint (i : Fin 2) : C ⟶ relativeCylinder C where
  functor := CategoryTheory.Prod.sectR i C.category
  map := fun _ _ _ hf => hf

/-- 概要：同じ端点の射影は恒等関手（HA §1.3.4）。
方針：積の第二成分で計算する。
規約：相対関手の等式。使われ方：端点の全関手圏での比較。 -/
lemma relativeCylinderEndpoint_projection (i : Fin 2) :
    relativeCylinderEndpoint C i ≫ relativeCylinderProjection C = 𝟙 C := by
  apply relativeFunctor_ext
  rfl

/-- 概要：同じ零端点から円筒の恒等への比較（HA §1.3.4）。
方針：区間の零から各点への一意の射を使う。
規約：第二成分は同じ恒等射。使われ方：射影の弱逆の比較。 -/
def relativeCylinderContraction :
    (relativeCylinderProjection C).functor ⋙ (relativeCylinderEndpoint C 0).functor ⟶
      𝟭 (relativeCylinder C).category where
  app X := (homOfLE (Fin.zero_le X.1), 𝟙 X.2)
  naturality X Y f := by
    apply Prod.ext
    · apply Subsingleton.elim
    · exact Category.comp_id _ |>.trans (Category.id_comp _).symm

/-- 概要：同じ円筒の縮約は全成分が指定弱射（HA §1.3.4）。
方針：第二成分が恒等射であることを使う。
規約：元の指定弱射。使われ方：局所化後の全関手の同値。 -/
lemma relativeCylinderContraction_weak (X : (relativeCylinder C).category) :
    (relativeCylinder C).weakEquivalences ((relativeCylinderContraction C).app X) :=
  C.isMultiplicative.id_mem X.2

/-- 概要：同じ円筒の射影の局所化は準圏同値（HA §1.3.4）。
方針：元の零端点と同じ弱縮約を局所化の比較則に渡す。
規約：射影の実関手自身。使われ方：両端点の比較を全関手圏へ移す。 -/
lemma relativeCylinderProjection_isQCatEquivalence :
    IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (relativeCylinderProjection C)) := by
  apply localizationNerveMap_isQCatEquivalence_of_weak_comparisons
    (relativeCylinderProjection C) (relativeCylinderEndpoint C 0)
    (relativeCylinderContraction C) (relativeCylinderContraction_weak C)
    (eqToHom (congrArg LocalizerMorphism.functor (relativeCylinderEndpoint_projection C 0)))
  intro X
  exact C.isMultiplicative.id_mem X

end SerrePositivity.EInfinity.Modules
