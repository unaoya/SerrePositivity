module

public import SerrePositivity.EInfinity.Hammock.FixedObjectLocalizationValue

/-!
# 固定対象の hammock の局所化 Hom への自然な評価

概要：各 zigzag の局所化での値を全語の余極限へ降ろす。
方針：全相対作用素の自然性を元の余極限の標準射で検査する。
規約：元の固定対象と全語・全作用素を保持する。
使われ方：自由相対解像の対角から既存 DK Hom への右比較。
-/

@[expose] public section
universe u uI vI uO
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FixedObjectDiagram.LocalizationObjects
open CategoryTheory CategoryTheory.Limits SimplicialLocalization

variable {I : Type uI} [Category.{vI} I] {D : I ⥤ RelativeCategory.{u}}
  {O : Type uO} (T : LocalizationObjects D O)

def homTransport (i : I) (X Y : O) :
    ((D.obj i).weakEquivalences.Q.obj (T.original i X) ⟶
      (D.obj i).weakEquivalences.Q.obj (T.original i Y)) ⟶
        (T.localized i X ⟶ T.localized i Y) :=
  ↾fun f => eqToHom (T.image_eq i X).symm ≫ f ≫ eqToHom (T.image_eq i Y)

def graphValue (i : I) (w : Word) (X Y : O) :
    Hammock.graph (D.obj i).weakEquivalences w (T.original i X) (T.original i Y) ⟶
      (T.homSimplicialDiagram X Y).obj i :=
  Zigzag.Value.graphMap (D.obj i).weakEquivalences.Q
    (D.obj i).weakEquivalences.Q_inverts ≫
      (Functor.const SimplexCategoryᵒᵖ).map (T.homTransport i X Y)

def colimitValue (i : I) (X Y : O) :
    colimitGraph (D.obj i).weakEquivalences (T.original i X) (T.original i Y) ⟶
      (T.homSimplicialDiagram X Y).obj i :=
  Zigzag.Value.colimitValue (D.obj i).weakEquivalences.Q
    (D.obj i).weakEquivalences.Q_inverts (T.original i X) (T.original i Y) ≫
      (Functor.const SimplexCategoryᵒᵖ).map (T.homTransport i X Y)

lemma colimitValue_fac (i : I) (X Y : O) (w : Word) :
    graphInclusion (D.obj i).weakEquivalences (T.original i X) (T.original i Y) w ≫
      T.colimitValue i X Y = T.graphValue i w X Y := by
  dsimp only [colimitValue, graphValue]
  rw [← Category.assoc, Zigzag.Value.graphInclusion_colimitValue]

def graphEvaluation (w : Word) (X Y : O) :
    graphDiagram D T.original (fun θ X => T.original_naturality θ X) w X Y ⟶
      T.homSimplicialDiagram X Y where
  app i := T.graphValue i w X Y
  naturality i j θ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro τ
    change T.value j ((Zigzag.Relative.fixedFunctor (D.map θ)
      (T.original_naturality θ X) (T.original_naturality θ Y)).obj (τ.obj 0)) =
        FixedObjectHom.map (D ⋙ strictLocalizationFunctor) T.localized
          (fun θ X => T.localized_naturality θ X) θ (T.value i (τ.obj 0))
    exact T.value_naturality θ (τ.obj 0)

def hammockEvaluation (X Y : O) : T.hammockDiagram X Y ⟶ T.homSimplicialDiagram X Y where
  app i := T.colimitValue i X Y
  naturality i j θ := by
    apply colimitGraph_hom_ext (D.obj i).weakEquivalences (T.original i X) (T.original i Y)
    intro w
    let η := ((graphWordDiagram D T.original
      (fun θ X => T.original_naturality θ X) X Y).flip).map θ
    have hι := colimit.ι_map η w
    change graphInclusion (D.obj i).weakEquivalences (T.original i X) (T.original i Y) w ≫
      (T.hammockDiagram X Y).map θ = η.app w ≫
        graphInclusion (D.obj j).weakEquivalences (T.original j X) (T.original j Y) w at hι
    calc
      graphInclusion _ _ _ w ≫ ((T.hammockDiagram X Y).map θ ≫ T.colimitValue j X Y) =
          η.app w ≫ (graphInclusion _ _ _ w ≫ T.colimitValue j X Y) := by
            simpa only [Category.assoc] using congrArg (fun f => f ≫ T.colimitValue j X Y) hι
      _ = η.app w ≫ T.graphValue j w X Y := by rw [T.colimitValue_fac]
      _ = T.graphValue i w X Y ≫ (T.homSimplicialDiagram X Y).map θ :=
        (T.graphEvaluation w X Y).naturality θ
      _ = graphInclusion _ _ _ w ≫
          (T.colimitValue i X Y ≫ (T.homSimplicialDiagram X Y).map θ) := by
        rw [← Category.assoc, T.colimitValue_fac]

end SerrePositivity.EInfinity.Hammock.FixedObjectDiagram.LocalizationObjects
