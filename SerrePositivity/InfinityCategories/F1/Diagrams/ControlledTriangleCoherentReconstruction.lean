module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleUniversalLongHom
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleSeparatedFamilyShortFaces
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleSeparatedFamilyDiagonal

/-!
概要：要求正本の実 L の全てをパラメーターにした、標準全対角を持つ実二胞体族。
方針：普遍長 Hom の対角を保つ Kan 延長を選び、全次数で組み立てる。
規約：元の二短辺と標準全対角を全 K・L で厳密に回収する。
使われ方：固定ホーン fiber への実 encode の構成。単射性と厳密切断は別途。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (X Y Z : KanObject.{u}) (K : SSet.{u + 1})
  (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
  (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))

def controlledTriangleSeparatedExtension :
    let L := controlledTriangleLongHomSpace X Z K (controlledTriangleCompositeFamily X Y Z K f g)
    (Δ[1] : SSet.{u + 1}) ⊗ ((K ⊗ K) ⊗ L) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z) :=
  (controlledTriangleUniversalSeparatedExtension_exists X Y Z K f g).choose

lemma controlledTriangleSeparatedExtension_comp :
    let L := controlledTriangleLongHomSpace X Z K (controlledTriangleCompositeFamily X Y Z K f g)
    prismEndpoint 1 ((K ⊗ K) ⊗ L) ≫ controlledTriangleSeparatedExtension X Y Z K f g =
      lift (fst (K ⊗ K) L ≫ fst K K ≫ f) (fst (K ⊗ K) L ≫ snd K K ≫ g) ≫
      (HomotopyLimits.uliftTensorIso.{u, u + 1}
        (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (eComp SSet X Y Z) :=
  (controlledTriangleUniversalSeparatedExtension_exists X Y Z K f g).choose_spec.2

lemma controlledTriangleSeparatedExtension_diagonal :
    let c := controlledTriangleCompositeFamily X Y Z K f g
    let L := controlledTriangleLongHomSpace X Z K c
    (Δ[1] ◁ triangleParameterDiagonal K L) ≫ controlledTriangleSeparatedExtension X Y Z K f g =
      uncurry (controlledTriangleUniversalInterval X Z K c) :=
  (controlledTriangleUniversalSeparatedExtension_exists X Y Z K f g).choose_spec.1

/-- 同じ実 L 全体での再構成二胞体族。 -/
def controlledTriangleCoherentFamily :
    let L := controlledTriangleLongHomSpace X Z K (controlledTriangleCompositeFamily X Y Z K f g)
    (Δ[2] : SSet.{u + 1}) ⊗ (K ⊗ L) ⟶ SpaceInfinity.{u} :=
  triangleSeparatedFamily f g (controlledTriangleSeparatedExtension X Y Z K f g)
    (controlledTriangleSeparatedExtension_comp X Y Z K f g)

lemma controlledTriangleCoherentFamily_first :
    let L := controlledTriangleLongHomSpace X Z K (controlledTriangleCompositeFamily X Y Z K f g)
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ L)) ≫ controlledTriangleCoherentFamily X Y Z K f g =
      intervalMappingUncurry (fst K L ≫ f ≫ coherentHomIntervalComparison X Y) :=
  triangleSeparatedFamily_first f g _ (controlledTriangleSeparatedExtension_comp X Y Z K f g)

lemma controlledTriangleCoherentFamily_last :
    let L := controlledTriangleLongHomSpace X Z K (controlledTriangleCompositeFamily X Y Z K f g)
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ L)) ≫ controlledTriangleCoherentFamily X Y Z K f g =
      intervalMappingUncurry (fst K L ≫ g ≫ coherentHomIntervalComparison Y Z) :=
  triangleSeparatedFamily_last f g _ (controlledTriangleSeparatedExtension_comp X Y Z K f g)

/-- 実 L の同じ普遍長 Hom の直接評価を、全 K・L の標準 coherent 長辺として厳密回収。 -/
lemma controlledTriangleCoherentFamily_diagonal :
    let c := controlledTriangleCompositeFamily X Y Z K f g
    let L := controlledTriangleLongHomSpace X Z K c
    (stdSimplex.δ (1 : Fin 3) ▷ (K ⊗ L)) ≫ controlledTriangleCoherentFamily X Y Z K f g =
      (Δ[1] ◁ (prismEndpoint 0 (K ⊗ L) ≫ uncurry (controlledTriangleUniversalInterval X Z K c))) ≫
        intervalMappingUncurry (coherentHomIntervalComparison X Z) :=
  triangleSeparatedFamily_diagonal f g _ (controlledTriangleSeparatedExtension_comp X Y Z K f g)
    _ (controlledTriangleSeparatedExtension_diagonal X Y Z K f g)

end SerrePositivity.InfinityCategories
