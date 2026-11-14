module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardFamilyFunctor

/-!
# 元の中央の自然な脚の関手的分解と comma 図式

概要：元の中央の全射を同じ関手的分解へ渡し、置換対象も動く comma 図式を作る。
方針：中央の自然変換から Arrow の図式を作り、分解の p の自然性を使う。
規約：モデル圏だけから関手的分解を仮定せず、同じ指定分解を明示入力とする。
使われ方：左ブロック全体の置換関手と元の射影自然変換。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFactorizationInput
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {X Y : C} (F : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family D C n m X Y)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

def middleArrow : D ⥤ Arrow C where
  obj d := Arrow.mk (F.middle.app d)
  map f := Arrow.homMk ((F.right.map f).app 0) ((F.left.map f).app (Fin.last n))
    (F.middle.naturality f)
  map_id d := by
    apply Arrow.hom_ext
    · change (F.right.map (𝟙 d)).app 0 = 𝟙 _
      rw [F.right.map_id]
      rfl
    · change (F.left.map (𝟙 d)).app (Fin.last n) = 𝟙 _
      rw [F.left.map_id]
      rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · change (F.right.map (f ≫ g)).app 0 = (F.right.map f).app 0 ≫ (F.right.map g).app 0
      rw [F.right.map_comp]
      rfl
    · change (F.left.map (f ≫ g)).app (Fin.last n) =
        (F.left.map f).app (Fin.last n) ≫ (F.left.map g).app (Fin.last n)
      rw [F.left.map_comp]
      rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFactorizationInput (middleArrow)


def pullbackInputs : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n where
  obj d := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFactorization.input cof (F.left.obj d) (F.middle.app d)
  map f :=
    { left := cof.Z.map (F.middleArrow.map f)
      right := F.left.map f
      w := cof.p.naturality (F.middleArrow.map f) }
  map_id d := by
    apply Comma.hom_ext
    · change cof.Z.map (F.middleArrow.map (𝟙 d)) = 𝟙 _
      rw [F.middleArrow.map_id, cof.Z.map_id]
    · exact F.left.map_id d
  map_comp f g := by
    apply Comma.hom_ext
    · change cof.Z.map (F.middleArrow.map (f ≫ g)) =
        cof.Z.map (F.middleArrow.map f) ≫ cof.Z.map (F.middleArrow.map g)
      rw [F.middleArrow.map_comp, cof.Z.map_comp]
    · exact F.left.map_comp f g

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFactorizationInput (pullbackInputs)


def pullbackLeft : D ⥤ ComposableArrows C n := F.pullbackInputs cof ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackFunctor

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFactorizationInput (pullbackLeft)


def pullbackLeftProjection : F.pullbackLeft cof ⟶ F.left where
  app d := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection ((F.pullbackInputs cof).obj d)
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection_naturality ((F.pullbackInputs cof).map f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFactorizationInput (pullbackLeftProjection)


lemma pullbackLeftProjection_trivialFibration (d : D) (i : Fin (n + 1)) :
    trivialFibrations C (((F.pullbackLeftProjection cof).app d).app i) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPullbackProjection_trivialFibration _ (cof.hp _) i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFactorizationInput (pullbackLeftProjection_trivialFibration)


lemma pullbackLeft_map_weak {d d' : D} (f : d ⟶ d') (i : Fin (n + 1)) :
    weakEquivalences C (((F.pullbackLeft cof).map f).app i) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPullbackComparison_weakEquivalence _ (cof.hp _) (cof.hp _) (F.left_mem f) i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFactorizationInput (pullbackLeft_map_weak)


end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFactorizationInput
