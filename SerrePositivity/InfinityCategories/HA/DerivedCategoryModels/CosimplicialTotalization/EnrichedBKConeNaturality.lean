module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.PointwiseBKConeNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.EnrichedBousfieldKanCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DoldKanClosedPrecomposition

/-!
概要：元の実豊穣Homに値を取るBK錐の双方向自然性。
方針：指定Γ Hom同型の前後合成則で、点ごとのΓの同じ等式を移す。
規約：IS-W2 D01の既存構成の自然性・係数移送則。元の全単体作用を保持。
使われ方：HA 1.2.4、指定native Tot錐の全図式パラメータへの組み立て。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory HomologicalComplex Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.EInfinity.ComplexLimits
variable {A : Type u} [CommRing A]

/-- 指定頂点Pから元の図式への実豊穣Homの全図式。 -/
def enrichedBKHomDiagram (P : Complex A) (X : CosimplicialObject (Complex A)) :
    SimplexCategoryᵒᵖᵒᵖ ⥤ SSet.{u} :=
  doubleOppositeDiagram X ⋙ complexToClosed A ⋙
    (SimplicialCategory.sHomFunctor (ClosedCategory A (Complex A))).obj
      (op (ForgetEnrichment.of (Complex A) P))

/-- 同じ実豊穣Homと点ごとのΓ Homの指定同型。 -/
def enrichedBKHomIso (P : Complex A) (X : CosimplicialObject (Complex A)) :
    enrichedBKHomDiagram P X ≅ (pointwiseBKSetHomFunctor A).obj
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) :=
  Functor.isoWhiskerLeft (doubleOppositeDiagram X) (complexDoldKanHomIso A P)

/-- 元の図式射の同じ実豊穣後合成。 -/
def enrichedBKHomTargetMap (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    enrichedBKHomDiagram P X ⟶ enrichedBKHomDiagram P Y :=
  Functor.whiskerRight
    (Functor.whiskerRight (Functor.whiskerLeft (opOpEquivalence SimplexCategory).functor f)
      (complexToClosed A))
    ((SimplicialCategory.sHomFunctor (ClosedCategory A (Complex A))).obj
      (op (ForgetEnrichment.of (Complex A) P)))

/-- 元の頂点の複体射の同じ実豊穣前合成。 -/
def enrichedBKHomSourceMap {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) :
    enrichedBKHomDiagram Q X ⟶ enrichedBKHomDiagram P X :=
  Functor.whiskerLeft (doubleOppositeDiagram X ⋙ complexToClosed A)
    ((SimplicialCategory.sHomFunctor (ClosedCategory A (Complex A))).map
      ((complexToClosed A).map f).op)

/-- 指定Hom同型は元の図式射の後合成に自然。 -/
theorem enrichedBKHomIso_target_naturality (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    enrichedBKHomTargetMap P f ≫ (enrichedBKHomIso P Y).hom =
      (enrichedBKHomIso P X).hom ≫
        (pointwiseBKSetHomFunctor A).map (normalizedBKConeTargetMap P f) := by
  apply NatTrans.ext
  funext j
  exact (complexDoldKanHomIso A P).hom.naturality
    (f.app ((opOpEquivalence SimplexCategory).functor.obj j))

/-- 指定Hom同型は元の頂点射の前合成に自然。 -/
theorem enrichedBKHomIso_source_naturality {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) :
    enrichedBKHomSourceMap f X ≫ (enrichedBKHomIso P X).hom =
      (enrichedBKHomIso Q X).hom ≫
        (pointwiseBKSetHomFunctor A).map (normalizedBKConeSourceMap f X) := by
  apply NatTrans.ext
  funext j
  exact complexDoldKanHomIso_precomposition f
    (X.obj ((opOpEquivalence SimplexCategory).functor.obj j))

/-- 元の実豊穣BK錐は、図式射と指定Tot射の同じ両作用に両立する。 -/
theorem enrichedBousfieldKanCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    enrichedBousfieldKanCone X ≫
        Functor.whiskerRight (enrichedBKHomTargetMap ((productTotalFunctor A).obj X) f)
          SimplicialObject.opFunctor =
      enrichedBousfieldKanCone Y ≫
        Functor.whiskerRight (enrichedBKHomSourceMap ((productTotalFunctor A).map f) Y)
          SimplicialObject.opFunctor := by
  let P := (productTotalFunctor A).obj X
  let Q := (productTotalFunctor A).obj Y
  let eX := Functor.isoWhiskerRight (enrichedBKHomIso P X) SimplicialObject.opFunctor
  let eY := Functor.isoWhiskerRight (enrichedBKHomIso Q Y) SimplicialObject.opFunctor
  let e := Functor.isoWhiskerRight (enrichedBKHomIso P Y) SimplicialObject.opFunctor
  have ht := congrArg (fun η => Functor.whiskerRight η SimplicialObject.opFunctor)
    (enrichedBKHomIso_target_naturality P f)
  have hs := congrArg (fun η => Functor.whiskerRight η SimplicialObject.opFunctor)
    (enrichedBKHomIso_source_naturality ((productTotalFunctor A).map f) Y)
  simp only [Functor.whiskerRight_comp] at ht hs
  apply (cancel_mono e.hom).mp
  change ((reflectedPointwiseBousfieldKanCone X ≫ eX.inv) ≫ _) ≫ e.hom =
    ((reflectedPointwiseBousfieldKanCone Y ≫ eY.inv) ≫ _) ≫ e.hom
  simp only [Category.assoc]
  erw [ht, hs]
  change reflectedPointwiseBousfieldKanCone X ≫ eX.inv ≫ eX.hom ≫
      Functor.whiskerRight ((pointwiseBKSetHomFunctor A).map
        (normalizedBKConeTargetMap P f)) SimplicialObject.opFunctor =
    reflectedPointwiseBousfieldKanCone Y ≫ eY.inv ≫ eY.hom ≫
      Functor.whiskerRight ((pointwiseBKSetHomFunctor A).map
        (normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y))
        SimplicialObject.opFunctor
  erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  exact reflectedPointwiseBousfieldKanCone_dinaturality A f

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
