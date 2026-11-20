module


public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PullbackKanSequence
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreeIntervalBoundary
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreePathSpace
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
概要：点つき射の mapping path による Kan fibration への因子分解。
方針：始点評価を射に沿って引き戻し、終点評価を新しい射とする。
規約：π_* 同型となる比較射は定数 path で与える。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。任意のスペクトルの射の置換。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき射の mapping path 対象。
方針：自由な path の始点評価を元の射に沿って引き戻す。
規約：始点は元の射の像、終点は自由。
使われ方：Goerss–Jardine I §7。任意の射の fibration 置換の全空間。 -/
abbrev mappingPath {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    PointedSimplicialSet.{u} := pullback (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f

/-- 概要：mapping path から元の源への射影。
方針：引き戻しの第二射影を取る。
規約：定数 path の比較射の左逆となる。
使われ方：BF 1978 §2、Goerss–Jardine I §7。π_* 同型の証明。 -/
def mappingPathRetraction {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath f ⟶ X :=
  pullback.snd (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f

/-- 概要：mapping path から元の標的への終点射。
方針：引き戻しの path 成分を終点で評価する。
規約：元の射の fibration 置換の右因子。
使われ方：BF 1978 §2、Goerss–Jardine I §7。任意の射の fiber の構成。 -/
def mappingPathProjection {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath f ⟶ Y :=
  pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 0

/-- 概要：mapping path の源への射影は全ての単射に RLP を持つ。
方針：始点評価の RLP を引き戻す。
規約：標的 Y の Kan 性だけで十分。
使われ方：Goerss–Jardine I §7、HTT A.3.3。比較射の π_* 同型。 -/
theorem mappingPathRetraction_rlp {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    [KanComplex Y.right] : (MorphismProperty.monomorphisms SSet.{u}).rlp
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f).right :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_snd_rlp _ _ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint_rlp Y 1)

/-- 概要：mapping path の終点射は Kan fibration。
方針：源の成分のホーンを先に充填し、次に path の両端点を同時に充填する。
規約：X と Y の Kan 性を要求する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。任意の射の fibration 置換。 -/
instance mappingPathProjection_fibration {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    [KanComplex X.right] [KanComplex Y.right] : Fibration (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f).right := by
  apply (fibration_iff _).2
  intro A B j hj
  let : HasLiftingProperty j (terminal.from X.right) :=
    ((fibration_iff _).1 inferInstance) j hj
  let : HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints Y) :=
    ((fibration_iff _).1 inferInstance) j hj
  constructor
  intro a b sq
  let pb := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f
  let sqX : CommSq (a ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f).right) j (terminal.from X.right)
      (terminal.from B) := ⟨terminal.hom_ext _ _⟩
  let sqP : CommSq (a ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right) j
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints Y) (prod.lift b (sqX.lift ≫ f.right)) := by
    constructor
    apply prod.hom_ext
    · have hw : a ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right ≫
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 0).right = j ≫ b := sq.w
      simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints_fst, prod.lift_fst] using hw
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints_snd, prod.lift_snd]
      rw [← Category.assoc j sqX.lift f.right, sqX.fac_left, Category.assoc]
      exact congrArg (a ≫ ·) pb.w
  have h : sqP.lift ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1).right = sqX.lift ≫ f.right := by
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints_snd, ← Category.assoc, sqP.fac_right, prod.lift_snd]
  let l := pb.lift sqP.lift sqX.lift h
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply pb.hom_ext
    · rw [Category.assoc, IsPullback.lift_fst]
      exact sqP.fac_left
    · rw [Category.assoc, IsPullback.lift_snd]
      exact sqX.fac_left
  · change l ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 0).right = b
    rw [← Category.assoc, IsPullback.lift_fst, ← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoints_fst,
      ← Category.assoc, sqP.fac_right, prod.lift_fst]

/-- 概要：元の源から mapping path への定数 path の比較射。
方針：元の射の値で定数な path と恒等射を引き戻しへ貼る。
規約：元の射の因子分解の左因子。
使われ方：BF 1978 §2、Goerss–Jardine I §7。任意の射の厳密な置換。 -/
def mappingPathUnit {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) : X ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath f :=
  pullback.lift (f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath Y) (𝟙 X) (by simp)

/-- 概要：定数 path の比較射と源への射影の合成は恒等射。
方針：引き戻しの第二射影の計算式を使う。
規約：点つき射の厳密な等式。
使われ方：BF 1978 §2。比較射の π_* 同型。 -/
@[reassoc (attr := simp)]
theorem mappingPathUnit_retraction {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f = 𝟙 _ := pullback.lift_snd ..

/-- 概要：定数 path の比較射と終点射の合成は元の射。
方針：第一射影を計算し、定数 path の終点評価を使う。
規約：ホモトピーを介さない厳密な因子分解。
使われ方：BF 1978 §2、Goerss–Jardine I §7。任意の射の置換。 -/
@[reassoc (attr := simp)]
theorem mappingPathUnit_projection {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f = f := by
  simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit, pullback.lift_fst_assoc,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath_endpoint, Category.comp_id]

end

end SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
