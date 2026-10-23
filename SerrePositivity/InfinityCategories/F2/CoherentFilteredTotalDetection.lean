module

public import SerrePositivity.InfinityCategories.F2.FilteredLeftFibrationDetection
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningFiber

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

/-- 概要：一般 coherent な空間値図式の小さい全空間の Kan 置換。
方針：既存の小さい left unstraightening を具体的な連続置換で送る。
規約：余極限性を定義の一部として要求しない。使われ方：一般図式の候補模型。 -/
def coherentDiagramTotalKan
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) : SSet.{u} :=
  continuousKanReplacement.obj (smallLeftUnstraightening F)

/-- 概要：全空間の置換は Kan 複体。
方針：具体的な連続置換の充填性を使う。
規約：底の filtered 性は不要。使われ方：有限射のホモトピー類の比較。 -/
instance coherentDiagramTotalKan_kanComplex
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    KanComplex (coherentDiagramTotalKan F) :=
  inferInstanceAs (KanComplex (continuousKanReplacement.obj (smallLeftUnstraightening F)))

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
