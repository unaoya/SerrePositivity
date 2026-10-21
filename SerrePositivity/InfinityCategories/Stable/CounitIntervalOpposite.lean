module
public import SerrePositivity.InfinityCategories.Stable.FunctorOppositeEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalFunctorOpposite
public import SerrePositivity.InfinityCategories.F1B.PointwiseUnitComparison
/-!
概要：実余単位の標準区間比較から反対側の指定単位条件を得る。
方針：同じ実ホモトピーを反転し、任意パラメータ族の合成表示で比較する。
規約：標準の写像空間比較と元の全関手を保持する。使われ方：一般 RHom の ∞ 随伴。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 同じ実余単位の反転が与える h Fun の指定単位。 -/
def counitOppositeUnitHom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (H : SSet.Homotopy (G ≫ F) (𝟙 Y)) :
    FunctorHom (𝟙 Y.op) (opFunctor.map G ≫ opFunctor.map F) :=
  F1B.kanFunctorOppositeHomEquiv (G ≫ F) (𝟙 Y)
    (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))

/-- 反転した指定単位の成分は、元の同じ余単位成分の反対。 -/
lemma counitOppositeUnitHom_component {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (G ≫ F) (𝟙 Y)) (y : Y _⦋0⦌) :
    qcatUnitComponent (counitOppositeUnitHom H) (SSet.opObjEquiv.symm y) =
      SSet.Truncated.HomotopyCategory.homMk (edgeOp (simplicialHomotopyVertexEdge H y)) := by
  unfold qcatUnitComponent counitOppositeUnitHom
  rw [functorOppositeHomEquiv_evaluate, functorHomEvaluate_homotopy,
    F1B.kanHomotopyCategoryOpHomEquiv_homMk]
  rfl

/-- 元の余単位の標準区間比較の反転は、反対側の指定単位比較とホモトピック。 -/
lemma counitIntervalReverse_homotopy {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (G ≫ F) (𝟙 Y)) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    Nonempty (SSet.Homotopy
      (intervalReverseFamily
        (intervalFunctorMap F x (G.app (Opposite.op ⦋0⦌) y) ≫
          intervalPostcompose (F.app (Opposite.op ⦋0⦌) x)
            (SSet.Truncated.HomotopyCategory.homMk (simplicialHomotopyVertexEdge H y).toTruncated)))
      ((HomotopyLimits.intervalOppositeIso x (G.app (Opposite.op ⦋0⦌) y)).hom ≫
        unitIntervalMap (counitOppositeUnitHom H) (SSet.opObjEquiv.symm y)
          (SSet.opObjEquiv.symm x))) := by
  let e := (simplicialHomotopyVertexEdge H y).toTruncated
  let m := intervalFunctorMap F x (G.app (Opposite.op ⦋0⦌) y)
  obtain ⟨K⟩ := HomotopyLimits.intervalReverseFamily_postcompose_hom
    (F.app (Opposite.op ⦋0⦌) x) e
  let K' := functorHomotopyPrecomp K (opFunctor.map m)
  refine ⟨{ h := K'.h, h₀ := K'.h₀.trans ?_, h₁ := K'.h₁.trans ?_, rel := K'.rel }⟩
  · exact (intervalReverseFamily_precomp m _).symm
  · change opFunctor.map m ≫ (HomotopyLimits.intervalOppositeIso
      (F.app (Opposite.op ⦋0⦌) x)
      (F.app (Opposite.op ⦋0⦌) (G.app (Opposite.op ⦋0⦌) y))).hom ≫ _ = _
    rw [← Category.assoc, HomotopyLimits.intervalOppositeIso_naturality]
    simp only [Category.assoc, unitIntervalMap, counitOppositeUnitHom_component]
    rfl

/-- 同じ余単位の全区間比較の同値性から、反対側の標準単位条件を得る。 -/
lemma counitOppositeUnitHom_mappingSpaceCondition {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (G ≫ F) (𝟙 Y))
    (h : ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), IsSimplicialHomotopyEquivalence
      (intervalFunctorMap F x (G.app (Opposite.op ⦋0⦌) y) ≫
        intervalPostcompose (F.app (Opposite.op ⦋0⦌) x)
          (SSet.Truncated.HomotopyCategory.homMk (simplicialHomotopyVertexEdge H y).toTruncated))) :
    UnitMappingSpaceCondition (counitOppositeUnitHom H) := by
  rw [unitMappingSpaceCondition_iff_interval]
  intro y x
  let x' := SSet.opObjEquiv x
  let y' := SSet.opObjEquiv y
  let m := intervalFunctorMap F x' (G.app (Opposite.op ⦋0⦌) y') ≫
    intervalPostcompose (F.app (Opposite.op ⦋0⦌) x')
      (SSet.Truncated.HomotopyCategory.homMk (simplicialHomotopyVertexEdge H y').toTruncated)
  have hm := F1B.kanIsQCatEquivalence_op (h x' y').isQCatEquivalence
  have hi := (qCatEquivalenceOfIso (HomotopyLimits.intervalOppositeIso
    (F.app (Opposite.op ⦋0⦌) x') y')).isQCatEquivalence
  have hr := hm.comp hi
  change IsQCatEquivalence (opFunctor.map m ≫
    (HomotopyLimits.intervalOppositeIso (F.app (Opposite.op ⦋0⦌) x') y').hom) at hr
  have he := HomotopyLimits.intervalReverseFamily_eq
    (F.app (Opposite.op ⦋0⦌) x') y' m
  rw [← he] at hr
  obtain ⟨K⟩ := counitIntervalReverse_homotopy H x' y'
  have ht := hr.ofFunctorIso (functorIsoOfSimplicialHomotopy K)
  exact ((qCatEquivalenceOfIso (HomotopyLimits.intervalOppositeIso x'
    (G.app (Opposite.op ⦋0⦌) y'))).isQCatEquivalence.cancel_left ht).isSimplicialHomotopyEquivalence
end SerrePositivity.InfinityCategories
