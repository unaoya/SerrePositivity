module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorNaturality

/-!
概要：相対関手空間の縮小と任意の小さい始域への制限が厳密に可換。
方針：標的だけを縮小する同型を作り、全単体で共役と前合成を照合する。
規約：底上の射と全パラメータを保持。使われ方：指定三角形比較の小宇宙下降。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 始域と底だけを宇宙持ち上げし、標的の縮小同型を相対写像空間へ作用させる。 -/
def smallUnstraighteningSourceRelativeIso {B C : SSet.{u}}
    (G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (a : C ⟶ B) :
    (SSet.uliftFunctor.{u + 1, u}).obj
        (relativeFunctorSpace (smallLeftUnstraighteningProjection G) a) ≅
      relativeFunctorSpace (leftUnstraighteningProjection G)
        ((SSet.uliftFunctor.{u + 1, u}).map a) :=
  uliftRelativeFunctorIso (smallLeftUnstraighteningProjection G) a ≪≫
    relativeFunctorOverIso (Iso.refl (Over.mk ((SSet.uliftFunctor.{u + 1, u}).map a)))
      (smallLeftUnstraighteningOverIso G)

/-- 小さい始域の包含を元の全空間への底上の射に持ち上げる。 -/
def smallUnstraighteningSourceRestriction {B C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (s : C ⟶ smallLeftUnstraightening F) :
    Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (s ≫ smallLeftUnstraighteningProjection F)) ⟶
      Over.mk (leftUnstraighteningProjection F) :=
  Over.homMk ((SSet.uliftFunctor.{u + 1, u}).map s ≫ (smallLeftUnstraighteningIso F).hom) (by
    change ((SSet.uliftFunctor.{u + 1, u}).map s ≫
      (smallLeftUnstraighteningIso F).hom) ≫ leftUnstraighteningProjection F =
        (SSet.uliftFunctor.{u + 1, u}).map (s ≫ smallLeftUnstraighteningProjection F)
    rw [Category.assoc, smallLeftUnstraighteningIso_projection, ← Functor.map_comp])

/-- 元の相対関手空間の縮小と任意の小さい始域への制限の厳密な交換式。 -/
lemma smallRelativeFunctorIso_inv_pre {B C : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (s : C ⟶ smallLeftUnstraightening F) :
    (smallLeftUnstraighteningRelativeFunctorIso F G).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (relativeFunctorPre (smallLeftUnstraighteningProjection G)
            (smallLeftUnstraighteningProjection F) s) =
      relativeFunctorOverPre (leftUnstraighteningProjection G)
        (smallUnstraighteningSourceRestriction F s) ≫
      (smallUnstraighteningSourceRelativeIso G (s ≫ smallLeftUnstraighteningProjection F)).inv := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro h
  apply ULift.ext
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro z
  rfl

end SerrePositivity.InfinityCategories.F2
