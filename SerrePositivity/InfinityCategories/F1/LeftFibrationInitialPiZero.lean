module
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Core.LeftFiberKan
public import SerrePositivity.InfinityCategories.Core.MappingSpaceLeft
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationInitialSpan

/-! # 始対象を持つ left fibration の fiber の連結成分

概要：始対象 c を持つ left fibration の y 上の fiber の連結成分は Hom(p(c), y) と同値。
方針：二つの自明 Kan fibration の比較 span を π₀ に移し、左 pinched 模型の Hom 同値を使う。
規約：基底は quasicategory。使われ方：固定終点余錐空間の Hom による表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：Kan 複体間の自明 Kan fibration は連結成分の同値を与える。
方針：明示的なホモトピー同値による π₀ の全単射を同値のデータにする。
規約：順方向は与えられた射の π₀ への作用。使われ方：比較 span の二射影の反転。 -/
def stablePiZeroEquivOfTrivialKanFibration {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [TrivialKanFibration p] : SSet.π₀ E ≃ SSet.π₀ B :=
  Equiv.ofBijective (SSet.mapπ₀ p)
    (isQCatEquivalence_of_trivialKanFibration p).isSimplicialHomotopyEquivalence.mapPiZero_bijective

/-- 概要：始対象 c を持つ left fibration の fiber の連結成分は Hom(p(c), y) と同値。
方針：始点固定の比較 span の二つの自明な射影を反転・合成し、底の左写像空間を Hom に移す。
規約：全空間の quasicategory 性は底の仮定から導く。使われ方：余極限頂点の表現可能性。 -/
def leftFibrationInitialFiberPiZeroEquiv {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (c : E _⦋0⦌) (hc : IsInitialVertex c) (y : B _⦋0⦌) :
    SSet.π₀ (vertexFiber p y) ≃
      ((SSet.HomotopyCategory.mk (p.app (Opposite.op ⦋0⦌) c) : hoFunctor.obj B) ⟶
        SSet.HomotopyCategory.mk y) := by
  have : KanComplex (vertexFiber p y) := vertexFiber_kanComplex_of_leftFibration p y
  have : KanComplex (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ p)) y) :=
    vertexFiber_kanComplex_of_leftFibration _ _
  have := leftFibrationInitialEvaluation_trivialKanFibration p c hc y
  let e := stablePiZeroEquivOfTrivialKanFibration (leftFibrationInitialEvaluation p c y)
  let f := stablePiZeroEquivOfTrivialKanFibration (leftFibrationInitialProjection p c y)
  let g := (SSet.π₀Functor.mapIso (leftFibrationInitialBaseIso p c y)).toEquiv
  exact e.symm.trans (f.trans (g.trans
    (pinchedHomLeftPiZeroEquiv (p.app (Opposite.op ⦋0⦌) c) y)))

/-- 概要：fiber と Hom の同値は、比較 span の中間空間からの二つの像を同一視する。
方針：連結成分の同値の定義中の逆同値と順同値を消す。
規約：中間空間の任意の連結成分。使われ方：比較の具体的な意味と自然性の証明。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_evaluation {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (c : E _⦋0⦌) (hc : IsInitialVertex c) (y : B _⦋0⦌)
    (a : SSet.π₀ (leftFibrationInitialTotal p c y)) :
    leftFibrationInitialFiberPiZeroEquiv p c hc y
        (SSet.mapπ₀ (leftFibrationInitialEvaluation p c y) a) =
      pinchedHomLeftPiZeroEquiv (p.app (Opposite.op ⦋0⦌) c) y
        (SSet.mapπ₀ (leftFibrationInitialBaseIso p c y).hom
          (SSet.mapπ₀ (leftFibrationInitialProjection p c y) a)) := by
  simp only [leftFibrationInitialFiberPiZeroEquiv, Equiv.trans_apply,
    stablePiZeroEquivOfTrivialKanFibration, Equiv.ofBijective_symm_apply_apply]
  rfl

end SerrePositivity.InfinityCategories
