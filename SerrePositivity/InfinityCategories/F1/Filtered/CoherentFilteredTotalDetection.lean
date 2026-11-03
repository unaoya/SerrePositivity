module
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentFilteredTotalDetection
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningFiber
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1B.KanComplex.HomotopyClasses
public import SerrePositivity.InfinityCategories.Core.Filtered.FilteredInfinity
public import SerrePositivity.InfinityCategories.F1.Filtered.FilteredLeftFibrationDetection


/-!
概要：一般 coherent な filtered 空間値図式の全空間模型を元の値から有限検出する。
方針：小さい unstraightening の Kan 置換を取り、fiber の値との同値を合成する。
規約：頂点ごとの比較射だけを構成する。余錐全体と余極限の普遍性は後続の証明課題。
使われ方：strict 図式を仮定しない filtered 余極限の模型の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}

/-- 概要：元の図式の各値から小さい全空間の Kan 置換への射。
方針：fiber 比較の逆射、全空間への包含、置換の単位を合成する。
規約：選択した fiber 比較に依存する頂点の射。使われ方：元の値による有限検出。 -/
def coherentDiagramValueToTotalKan
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up b))).obj ⟶
      coherentDiagramTotalKan F :=
  (smallLeftUnstraighteningFiberValueEquivalence F b).inv ≫
    vertexFiberι (smallLeftUnstraighteningProjection F) b ≫
      continuousKanReplacementUnit.app (smallLeftUnstraightening F)

/-- 概要：filtered な一般 coherent 図式の全空間模型への有限射は元の一つの値で表せる。
方針：fiber 検出の射を値の比較同値で移し、逆との合成のホモトピーを使う。
規約：元の指定射へのホモトピーを返す。使われ方：一般 coherent 余極限の有限検査。 -/
lemma coherentFilteredTotalKan_finite_value_detection [Quasicategory B] [IsFilteredInfinity B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    {K : SSet.{u}} [K.Finite] (f : K ⟶ coherentDiagramTotalKan F) :
    ∃ b : B _⦋0⦌,
      ∃ g : K ⟶ (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up b))).obj,
        Nonempty (SSet.Homotopy f (g ≫ coherentDiagramValueToTotalKan F b)) := by
  obtain ⟨b, g, ⟨H⟩⟩ := continuousKanLeftFibration_finite_fiber_detection_unreplaced
    (smallLeftUnstraighteningProjection F) f
  let e := smallLeftUnstraighteningFiberValueEquivalence F b
  refine ⟨b, g ≫ e.hom, (functorVertex_piZero_eq_iff_homotopy _ _).1 ?_⟩
  have h₁ := (functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨H⟩
  have h₂ := (functorVertex_piZero_eq_iff_homotopy _ _).2
    ⟨functorHomotopyPostcomp (functorHomotopyPrecomp e.homInvIso.simplicialHomotopy g)
      (vertexFiberι (smallLeftUnstraighteningProjection F) b ≫
        continuousKanReplacementUnit.app (smallLeftUnstraightening F))⟩
  simp only [Category.assoc, Category.id_comp] at h₂
  simpa only [coherentDiagramValueToTotalKan, Category.assoc] using h₁.trans h₂.symm

end SerrePositivity.InfinityCategories.F2
