module


public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping
public import SerrePositivity.Spectra.Pointed.Basic
public import SerrePositivity.Spectra.Pointed.InternalHom
public import SerrePositivity.Spectra.Pointed.Products
public import SerrePositivity.Spectra.Pointed.Smash
public import SerrePositivity.Spectra.Pointed.SmashAdjunction
public import SerrePositivity.Spectra.Pointed.SmashCurrying
public import SerrePositivity.Spectra.Pointed.SmashMonoidal
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
分割で生成：docstring を書き直すこと
概要：点つき写像空間の源の制限と smash の随伴の整合性。
方針：等化子への包含後に curry と smash の商の自然性を計算する。
規約：既存 Spectra の通常の smash・内部 Hom の基礎だけを借りる。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの厳密射との比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory

namespace SerrePositivity.KST.Spectra.PointedMapping
end SerrePositivity.KST.Spectra.PointedMapping
namespace SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets
open _root_.SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：指数の源の制限は定数写像を保つ。
方針：定数写像の curry を制限して計算する。
規約：点つき射でない基礎単体集合の射についても成立。
使われ方：HTT A.3.3。点つき制限の基点条件。 -/
theorem homBasepoint_pre {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    (Z : PointedSimplicialSet.{u}) :
    PointedObject.homBasepoint Y Z ≫ (MonoidalClosed.pre i.right).app Z.right =
      PointedObject.homBasepoint X Z := by
  dsimp only [PointedObject.homBasepoint]
  rw [MonoidalClosed.curry_pre_app]
  congr 1

/-- 概要：等化子による源の制限を点つき射として扱う。
方針：定数写像の保存を基点条件に使う。
規約：基礎単体集合の射は既に証明した pre と同じ。
使われ方：BF 1978 §2、HTT A.3.3。閉構造の制限との比較。 -/
def prePointed {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    (Z : PointedSimplicialSet.{u}) : PointedObject.basedHom Y Z ⟶ PointedObject.basedHom X Z :=
  Under.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Z) (by
    apply (cancel_mono (PointedObject.basedHomι X Z)).mp
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, ← Category.assoc, PointedObject.basedHom_basepoint_ι,
      PointedObject.basedHom_basepoint_ι]
    exact _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.homBasepoint_pre i Z)

/-- 概要：smash の第一変数の制限と点つき Hom の源の制限は随伴で対応する。
方針：smash の商へ引き戻して指数の curry の自然性を使う。
規約：源の単射性も Kan 性も不要。
使われ方：BF 1978 §2、HTT A.3.3。厳密なスペクトルの射の比較。 -/
theorem smashCurry_pre {X Y W Z : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    (f : PointedObject.smash Y W ⟶ Z) :
    PointedObject.smashCurry (PointedObject.smashMap i (𝟙 W) ≫ f) =
      PointedObject.smashCurry f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z := by
  apply Under.UnderMorphism.ext
  apply (cancel_mono (PointedObject.basedHomι X Z)).mp
  simp only [Under.comp_right, Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed, Under.homMk_right, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι,
    PointedObject.smashCurry_ι, PointedObject.smashCurry_ι_assoc]
  rw [MonoidalClosed.curry_pre_app]
  congr 1
  have h := congrArg Under.Hom.right (PointedObject.smashQuotient_map i (𝟙 W))
  simp only [Under.comp_right, PointedObject.prodMap_right, Under.id_right,
    tensorHom_id] at h
  rw [← Category.assoc, h, Category.assoc]

/-- 概要：等化子から作った制限は点つき閉構造の pre と一致する。
方針：評価射の curry を恒等射として、smash の第一変数の自然性を使う。
規約：同じ点つき内部 Hom の二つの構成を比較する。
使われ方：HTT A.3.3、BF 1978 §2。通常の射への制限の作用。 -/
theorem prePointed_eq_closedPre {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    (Z : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z = (MonoidalClosed.pre i).app Z := by
  have hc {P Q R : PointedSimplicialSet.{u}} (f : P ⊗ Q ⟶ R) :
      MonoidalClosed.curry f = PointedObject.smashCurry f := by
    change (PointedObject.smashHomAdjunction P).homEquiv Q R f = _
    simp only [PointedObject.smashHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  have h := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.smashCurry_pre i ((ihom.ev Y).app Z)
  simp only [← hc] at h
  change MonoidalClosed.curry (i ▷ ((ihom Y).obj Z) ≫ (ihom.ev Y).app Z) =
    MonoidalClosed.curry ((ihom.ev Y).app Z) ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z at h
  rw [← MonoidalClosed.uncurry_id_eq_ev, MonoidalClosed.curry_uncurry, Category.id_comp] at h
  rw [← h, MonoidalClosed.uncurry_id_eq_ev, ← MonoidalClosed.uncurry_pre,
    MonoidalClosed.curry_uncurry]

end

end SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
