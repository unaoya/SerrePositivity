module

public import SerrePositivity.InfinityCategories.F1.Coherent.SpaceSectionsObject
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningMappingSpace
public import SerrePositivity.InfinityCategories.F1.Universe.RelativeFunctor

/-!
概要：小さい unstraightening の全切断の宇宙持ち上げを、元の大きい全切断へ同定する。
方針：両側の切断を恒等図式上の相対関手へ移し、宇宙移送と全空間の縮小同型を使う。
規約：元の底は任意で、極限性は仮定しない。
使われ方：F1-4 の定値始域比較の標的を小さい Kan 対象へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 同じ全切断の小さい表示と元の大きい表示は厳密に同型。 -/
def smallUnstraighteningSectionsIso :
    (SSet.uliftFunctor.{u + 1, u}).obj (coherentSpaceSectionsObject F).obj ≅
      HomotopyLimits.simplicialSections (leftUnstraighteningProjection F) :=
  (SSet.uliftFunctor.{u + 1, u}).mapIso
      (HomotopyLimits.simplicialSectionsRelativeIso (smallLeftUnstraighteningProjection F)) ≪≫
    uliftRelativeFunctorIso (smallLeftUnstraighteningProjection F) (𝟙 B) ≪≫
    eqToIso (by rw [(SSet.uliftFunctor.{u + 1, u}).map_id]; rfl) ≪≫
    relativeFunctorOverIso (Iso.refl (Over.mk (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj B))))
      (smallLeftUnstraighteningOverIso F) ≪≫
    (HomotopyLimits.simplicialSectionsRelativeIso (leftUnstraighteningProjection F)).symm

end SerrePositivity.InfinityCategories
