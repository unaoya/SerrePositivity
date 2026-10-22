module
public import SerrePositivity.KST.Fibration.DiagramSumSource
public import SerrePositivity.KST.Fibration.SmallSpaceDiagram

/-! # 二つの元の空間値図式を、同じ小さい全充満標的に厳密に含める -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {X Y : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj Y ⟶ SpaceInfinity.{u})

/-- 二つの元の図式の和を、全ての同じ単体を保って構成する。 -/
def spaceDiagramSum :
    (SSet.uliftFunctor.{u + 1, u}).obj (diagramSumSource X Y) ⟶ SpaceInfinity.{u} where
  app n := ↾fun s => s.down.elim
    (fun x => F.app n (ULift.up x)) (fun y => G.app n (ULift.up y))
  naturality {n m} a := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x | y⟩
    · exact congrArg
        (fun k : ((SSet.uliftFunctor.{u + 1, u}).obj X).obj n ⟶ SpaceInfinity.obj m =>
          k (ULift.up.{u + 1, u} x)) (F.naturality a)
    · exact congrArg
        (fun k : ((SSet.uliftFunctor.{u + 1, u}).obj Y).obj n ⟶ SpaceInfinity.obj m =>
          k (ULift.up.{u + 1, u} y)) (G.naturality a)

/-- 第一図式を元の和から厳密に回収する。 -/
theorem spaceDiagramSum_inl :
    (SSet.uliftFunctor.{u + 1, u}).map (diagramSumInl X Y) ≫ spaceDiagramSum F G = F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x⟩
  rfl

/-- 第二図式も元の和から厳密に回収する。 -/
theorem spaceDiagramSum_inr :
    (SSet.uliftFunctor.{u + 1, u}).map (diagramSumInr X Y) ≫ spaceDiagramSum F G = G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨y⟩
  rfl

/-- 二つの図式を共通の小さい全充満標的に含めたときの、第一図式の小さい表示。 -/
def smallSpaceDiagramPairLeft : X ⟶ smallSpaceDiagramTarget (spaceDiagramSum F G) :=
  diagramSumInl X Y ≫ smallSpaceDiagram (spaceDiagramSum F G)

/-- 同じ共通の小さい全充満標的における第二図式の表示。 -/
def smallSpaceDiagramPairRight : Y ⟶ smallSpaceDiagramTarget (spaceDiagramSum F G) :=
  diagramSumInr X Y ≫ smallSpaceDiagram (spaceDiagramSum F G)

/-- 共通標的の同じ包含との合成は、第一の元の図式を厳密に回収する。 -/
theorem smallSpaceDiagramPairLeft_inclusion :
    (SSet.uliftFunctor.{u + 1, u}).map (smallSpaceDiagramPairLeft F G) ≫
      smallSpaceDiagramInclusion (spaceDiagramSum F G) = F := by
  rw [smallSpaceDiagramPairLeft, Functor.map_comp, Category.assoc,
    smallSpaceDiagram_inclusion, spaceDiagramSum_inl]

/-- 共通標的の同じ包含との合成は、第二の元の図式を厳密に回収する。 -/
theorem smallSpaceDiagramPairRight_inclusion :
    (SSet.uliftFunctor.{u + 1, u}).map (smallSpaceDiagramPairRight F G) ≫
      smallSpaceDiagramInclusion (spaceDiagramSum F G) = G := by
  rw [smallSpaceDiagramPairRight, Functor.map_comp, Category.assoc,
    smallSpaceDiagram_inclusion, spaceDiagramSum_inr]

end SerrePositivity.KST.Fibration
