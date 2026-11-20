module


public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.ModelCategory.Instances
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.OfMap
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
分割で生成：docstring を書き直すこと
概要：段ごとの Kan fibration に沿う Kan 列の引き戻し。
方針：点つき圏で段ごとに引き戻し、構造射を普遍性で貼る。
規約：構造射の単射性や Ω 条件はここでは主張しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。mapping path 列。
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

/-- 概要：点つきの引き戻しの基礎正方形は単体集合でも引き戻し。
方針：基点忘却の右随伴性から引き戻しの保存を使う。
規約：選んだ点つき極限の射の基礎射について述べる。
使われ方：HTT A.3.3、Goerss–Jardine I §7。右持ち上げ性の引き戻し。 -/
theorem pointedPullback_isPullback {E X B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (g : X ⟶ B) :
    IsPullback (pullback.fst f g).right (pullback.snd f g).right f.right g.right :=
  (IsPullback.of_hasPullback f g).map PointedSimplicialSet.forget

/-- 概要：点つき引き戻しの第二射影は全単射への RLP を保存する。
方針：基礎引き戻しと右持ち上げクラスの基底変換閉性を使う。
規約：元の第一の射について RLP を要求する。
使われ方：HTT A.3.3、Goerss–Jardine I §7。mapping path の比較射。 -/
theorem pointedPullback_snd_rlp {E X B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (g : X ⟶ B)
    (hf : (MorphismProperty.monomorphisms SSet.{u}).rlp f.right) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (pullback.snd f g).right :=
  (MorphismProperty.monomorphisms SSet.{u}).rlp.of_isPullback
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback f g) hf

/-- 概要：Kan fibration の点つき引き戻しの第二射影も Kan fibration。
方針：ホーン RLP の基底変換閉性を使う。
規約：標的 X に Kan 性は不要。
使われ方：Goerss–Jardine I §7、HTT A.3.3。引き戻しの段の Kan 性。 -/
instance pointedPullback_snd_fibration {E X B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (g : X ⟶ B) [Fibration f.right] :
    Fibration (pullback.snd f g).right := by
  apply (fibration_iff _).2
  exact J.rlp.of_isPullback (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback f g) ((fibration_iff _).1 inferInstance)

/-- 概要：Kan な底への Kan fibration の引き戻しの全空間は Kan。
方針：第二射影と底の終対象射の fibration を合成する。
規約：X の Kan 性だけを追加する。
使われ方：Goerss–Jardine I §7、HTT A.3.3。Kan 列の引き戻しの各段。 -/
instance pointedPullback_kanComplex {E X B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (g : X ⟶ B) [Fibration f.right] [KanComplex X.right] :
    KanComplex (pullback f g).right := by
  change Fibration (terminal.from (pullback f g).right)
  rw [show terminal.from (pullback f g).right =
    (pullback.snd f g).right ≫ terminal.from X.right from terminal.hom_ext _ _]
  infer_instance

end

end SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
