module
public import SerrePositivity.KST.Fibration.KanCommSqLimit
public import SerrePositivity.KST.Comparison.ExInfinityHomotopyPullback
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityKan
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquare
public import SerrePositivity.KST.Spectra.DiagramLimitExistenceTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeReindex

/-! # 元の通常の homotopy pullback 四角形から、全 coherent 四角形への接続 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Comparison
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration

/-- 元の Kan 四角形の全錐を、同じ cospan の horn 表示へ制限する。 -/
def kanCommSqHornCone {P X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    {a : P.obj ⟶ X.obj} {b : P.obj ⟶ Y.obj} {f : X.obj ⟶ Z.obj} {g : Y.obj ⟶ Z.obj}
    (sq : CommSq a b f g) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeRestrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqCone sq))
    CospanShape.strictCospanHornIso.{u, u + 1}.inv

/-- 元の全 Kan 錐から作る coherent 四角形。 -/
def kanCommSqInfinitySquare {P X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    {a : P.obj ⟶ X.obj} {b : P.obj ⟶ Y.obj} {f : X.obj ⟶ Z.obj} {g : Y.obj ⟶ Z.obj}
    (sq : CommSq a b f g) : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (kanCommSqHornCone sq)

/-- 全 coherent 四角形の左下の頂点は、元の Kan 四角形の元の頂点である。 -/
theorem kanCommSqInfinitySquare_apex {P X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    {a : P.obj ⟶ X.obj} {b : P.obj ⟶ Y.obj} {f : X.obj ⟶ Z.obj} {g : Y.obj ⟶ Z.obj}
    (sq : CommSq a b f g) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (kanCommSqInfinitySquare sq) 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex P := by
  rw [kanCommSqInfinitySquare, FiberModel.coneSquare_apex]
  change (Spectra.DiagramLimitTransport.restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqCone sq))
    CospanShape.strictCospanHornIso.inv).vertex = _
  rw [Spectra.DiagramLimitTransport.vertex_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_vertex]
  rfl

/-- 元の Kan 四角形が homotopy pullback なら、同じ全 coherent 四角形は ∞ 引き戻し。 -/
theorem kanCommSqInfinitySquare_isPullback {P X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    {a : P.obj ⟶ X.obj} {b : P.obj ⟶ Y.obj} {f : X.obj ⟶ Z.obj} {g : Y.obj ⟶ Z.obj}
    (sq : CommSq a b f g) (hsq : IsHomotopyPullback sq) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (kanCommSqInfinitySquare sq) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_isPullback _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeRestrict_isLimit_iff _ _).mp
    (kanCommSqCone_isLimit sq hsq))

/-- 任意の元の通常四角形を、同じ Ex∞ 射による全 coherent 四角形へ送る。 -/
def exInfinityCommSqInfinitySquare {P X Y Z : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : CommSq a b f g) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  kanCommSqInfinitySquare
    (P := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj P, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex P⟩)
    (X := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj X, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex X⟩)
    (Y := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj Y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex Y⟩)
    (Z := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj Z, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex Z⟩) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_commSq sq)

/-- 元の homotopy pullback 四角形は、同じ Ex∞ 後の全 coherent 引き戻しを与える。 -/
theorem exInfinityCommSqInfinitySquare_isPullback {P X Y Z : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : CommSq a b f g)
    (hsq : IsHomotopyPullback sq) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (exInfinityCommSqInfinitySquare sq) :=
  kanCommSqInfinitySquare_isPullback _ ((isHomotopyPullback_exInfinity_iff sq).mpr hsq)

end SerrePositivity.KST.Fibration
