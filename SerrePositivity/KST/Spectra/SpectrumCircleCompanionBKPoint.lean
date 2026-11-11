module

public import SerrePositivity.KST.Spectra.SpectrumCircleCompanionMapping
public import SerrePositivity.KST.Spectra.SpectrumCircleBKEndPoint
public import SerrePositivity.KST.Spectra.PointedCurryFamilyVertex

/-!
概要：元の companion の円の射を元の Hom–BK end へ送り、恒等射の BK 切断点と比較する。
方針：同じ円–BK 比較を成分の等式へ作用させ、単位射と元の写像族の頂点を照合する。
規約：元の固定 cospan の Hom 係数を保持。使われ方：元の円評価錐全体の表示との接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance companionBKPointSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance companionBKPointHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y
local instance companionBKPointEndKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex _

/-- 元の companion の円の射が表す、loop 写像空間の元の単位の点の射。 -/
def circleCompanionLoopPointMap (z : Sp.{u} _⦋0⦌) :
    𝟙_ SSet.{u} ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (circleEvaluationPointedHom z)).right :=
  PointedSimplicialSet.unitUnderlyingHom _ (curry' (circleEvaluationCompanionCircleMap z))

/-- companion の単位射の頂点は、元の companion の円の射が表す写像族の頂点。 -/
lemma circleCompanionLoopPointMap_vertex (z : Sp.{u} _⦋0⦌) :
    SSet.unitHomEquiv _ (circleCompanionLoopPointMap z) =
      PointedMapping.familyVertex (circleEvaluationCompanionCircleMap z) :=
  PointedMapping.unitUnderlyingHom_curry'_vertex _

/-- 元の普遍評価の単位射の頂点も、元の普遍評価の写像族の頂点そのもの。 -/
lemma circleEvaluationLoopPointMap_vertex (Y : OmegaSpectrum.{u}) :
    SSet.unitHomEquiv _ (circleEvaluationLoopPointMap Y) =
      PointedMapping.familyVertex (cotensorEvaluation PointedSimplicialSet.circle Y) :=
  PointedMapping.unitUnderlyingHom_curry'_vertex _

/-- 元の companion の円の射の点を、指定した元の Hom–BK 比較で送った切断点の射。 -/
def circleCompanionBKEndPointMap (z : Sp.{u} _⦋0⦌) :
    𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram
        (nativeCotensorInput PointedSimplicialSet.circle z).val)
        (cotensor PointedSimplicialSet.circle
          (nativeCotensorInput PointedSimplicialSet.circle z).val)) :=
  circleCompanionLoopPointMap z ≫ pointLoopCircleHomComparison
    (cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (nativeCotensorInput PointedSimplicialSet.circle z).val

/-- companion の同じ BK 切断点を、元の end の零単体として表示する。 -/
def circleCompanionBKEndPoint (z : Sp.{u} _⦋0⦌) :=
  SSet.unitHomEquiv _ (circleCompanionBKEndPointMap z)

/-- companion の BK 点は、元の cotensor 恒等射の BK 比較像と同じ成分。 -/
lemma circleCompanionBKEndPoint_component (z : Sp.{u} _⦋0⦌) :
    π₀.mk (circleCompanionBKEndPoint z) =
      π₀.mk (circleBKEndPoint (nativeCotensorInput PointedSimplicialSet.circle z).val) := by
  rw [circleCompanionBKEndPoint, circleBKEndPoint, circleCompanionBKEndPointMap,
    circleBKEndPointMap_factor, PointedMapping.unitHomEquiv_post,
    PointedMapping.unitHomEquiv_post, circleCompanionLoopPointMap_vertex,
    circleEvaluationLoopPointMap_vertex]
  have h := congrArg (mapπ₀ (pointLoopCircleHomComparison
    (cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (nativeCotensorInput PointedSimplicialSet.circle z).val))
        (circleEvaluationCompanionCircle_component z)
  simp only [mapπ₀_mk] at h
  exact h

/-- 元の Hom–BK end 内で companion の点から元の恒等射の比較像への実際の辺。 -/
def circleCompanionBKEndPointEdge (z : Sp.{u} _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val))).Edge
      (circleCompanionBKEndPoint z)
      (circleBKEndPoint (nativeCotensorInput PointedSimplicialSet.circle z).val) :=
  (nonempty_edge_of_piZero_eq (circleCompanionBKEndPoint_component z)).some

end SerrePositivity.KST.Spectra.OmegaSpectrum
