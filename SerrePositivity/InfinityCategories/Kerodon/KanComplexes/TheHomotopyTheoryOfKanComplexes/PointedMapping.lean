module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import SerrePositivity.Spectra.Pointed.Basic
public import SerrePositivity.Spectra.Pointed.InternalHom
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
概要：点つき単体集合の写像空間の Kan 性。
方針：既存の点つき対象の基礎定義だけを借り、指数の制限の相対ホーン充填を使う。
規約：既存 Spectra の安定モデル構造や HT-KQ は使わない。標的の Kan 性を明示する。
使われ方：Bousfield–Friedlander 1978 §2、HTT A.3.3、Kerodon §3.1.3（Tag 00TJ）。L9c の Hom。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.PointedMapping
end SerrePositivity.KST.Spectra.PointedMapping
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.KST.Spectra

namespace PointedMapping
open _root_.SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

/-- 概要：点つき単体集合の基点を与える射は単射。
方針：各次数の定義域が一元集合であることを使う。
規約：基点付き対象は既存の Under (𝟙_ SSet) を借りる。
使われ方：Kerodon §3.1.3（Tag 00TJ）。基点への制限が Kan fibration となる条件。 -/
theorem basepoint_mono (X : PointedSimplicialSet.{u}) : Mono X.hom := by
  have : ∀ n, Mono (X.hom.app n) := by
    intro n
    apply (mono_iff_injective _).2
    intro a b _
    change (a : PUnit.{u + 1}) = b
    exact @Subsingleton.elim PUnit.{u + 1} inferInstance a b
  exact NatTrans.mono_of_mono_app X.hom

/-- 概要：Kan な標的への写像を基点に制限する射は Kan fibration。
方針：基点包含の単射性と Mathlib の指数版 pushout-product を使う。
規約：標的の基礎単体集合の Kan 性だけを使う。
使われ方：Kerodon Corollary 3.1.3.3（Tag 00TM）、HTT A.3.3。点つき写像空間の充填。 -/
theorem restriction_fibration (X Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    Fibration (PointedObject.homRestriction X Y) := by
  let : Mono X.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basepoint_mono X
  change Fibration ((MonoidalClosed.pre X.hom).app Y.right)
  infer_instance

/-- 概要：Kan な点つき単体集合への点つき写像空間は Kan 複体。
方針：基点への制限の fibration に沿ってホーンを持ち上げ、その解を等化子へ戻す。
規約：源の Kan 性やスペクトルの Ω 条件は不要。
使われ方：Kerodon Corollary 3.1.3.3（Tag 00TM）、Bousfield–Friedlander 1978 §2。L9c の始段 Hom。 -/
instance basedHom_kanComplex (X Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    KanComplex (PointedObject.basedHom X Y).right := by
  let : Fibration (PointedObject.homRestriction X Y) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.restriction_fibration X Y
  rw [KanComplex.iff]
  intro n i fs hf
  let t := hf.desc
  have sq : CommSq (t ≫ PointedObject.basedHomι X Y) (horn (n + 1) i).ι
      (PointedObject.homRestriction X Y)
      (toUnit (Δ[n + 1] : SSet.{u}) ≫ PointedObject.homBasepoint PointedObject.point Y) := by
    constructor
    rw [Category.assoc, PointedObject.basedHomι_condition]
    change t ≫ PointedObject.basedHomι X Y ≫
        (toUnit _ ≫ PointedObject.homBasepoint PointedObject.point Y) = _
    simp only [comp_toUnit_assoc]
    rfl
  have heq : sq.lift ≫ PointedObject.homRestriction X Y =
      sq.lift ≫ PointedObject.homConstant X Y := by
    rw [sq.fac_right]
    change _ = sq.lift ≫ (toUnit _ ≫ PointedObject.homBasepoint PointedObject.point Y)
    simp only [comp_toUnit_assoc]
    rfl
  let l : (Δ[n + 1] : SSet.{u}) ⟶ (PointedObject.basedHom X Y).right :=
    equalizer.lift (f := PointedObject.homRestriction X Y) (g := PointedObject.homConstant X Y)
      sq.lift heq
  have hl : (horn (n + 1) i).ι ≫ l = t := by
    apply (cancel_mono (PointedObject.basedHomι X Y)).mp
    rw [Category.assoc]
    change (horn (n + 1) i).ι ≫ (equalizer.lift sq.lift heq ≫ equalizer.ι _ _) = _
    rw [equalizer.lift_ι]
    exact sq.fac_left
  refine ⟨l, fun j hj ↦ ?_⟩
  rw [← horn.ι_ι_assoc i j hj, hl]
  exact hf.ι_desc j hj

/-- 概要：点つき射に沿う指数の制限は基点評価と可換。
方針：指数の反変関手性と点つき射の可換条件を使う。
規約：ここでは基礎単体集合の射として述べる。
使われ方：HTT A.3.3、BF 1978 §2。Hom の制限の相対充填。 -/
@[reassoc]
theorem pre_restriction {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    (Z : PointedSimplicialSet.{u}) :
    (MonoidalClosed.pre i.right).app Z.right ≫ PointedObject.homRestriction X Z =
      PointedObject.homRestriction Y Z := by
  dsimp only [PointedObject.homRestriction]
  rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, Under.w i]

/-- 概要：点つき写像空間の源を点つき射で制限する。
方針：指数の制限を基点条件の等化子へ持ち上げる。
規約：基礎単体集合の射。単射性や Kan 性は定義には不要。
使われ方：BF 1978 §2、HTT A.3.3。切断スペクトルの Hom の遷移。 -/
def pre {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    (Z : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom Y Z).right ⟶ (PointedObject.basedHom X Z).right :=
  equalizer.lift (f := PointedObject.homRestriction X Z)
    (g := PointedObject.homConstant X Z)
    (PointedObject.basedHomι Y Z ≫ (MonoidalClosed.pre i.right).app Z.right) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_restriction, PointedObject.basedHomι_condition]
      dsimp only [PointedObject.homConstant]
      simp only [Category.assoc]
      rfl)

/-- 概要：点つき制限の包含後の写像は通常の指数の制限。
方針：等化子への持ち上げの計算則を使う。
規約：基礎単体集合の射の等式。
使われ方：BF 1978 §2。制限の相対充填と合成の計算。 -/
@[reassoc (attr := simp)]
theorem pre_ι {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    (Z : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Z ≫ PointedObject.basedHomι X Z =
      PointedObject.basedHomι Y Z ≫ (MonoidalClosed.pre i.right).app Z.right :=
  equalizer.lift_ι ..

/-- 概要：点つき制限の持ち上げは基礎指数の持ち上げから得られる。
方針：源の基点が制限先に含まれるので、充填した写像も基点条件を満たす。
規約：任意の左射についての右持ち上げ性。
使われ方：HTT A.3.3、BF 1978 §2。単射に沿う点つき Hom の fibration。 -/
theorem pre_hasLiftingProperty {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    (Z : PointedSimplicialSet.{u}) {A B : SSet.{u}} (j : A ⟶ B)
    [HasLiftingProperty j ((MonoidalClosed.pre i.right).app Z.right)] :
    HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Z) := by
  constructor
  intro a b sq
  let sq' : CommSq (a ≫ PointedObject.basedHomι Y Z) j
      ((MonoidalClosed.pre i.right).app Z.right) (b ≫ PointedObject.basedHomι X Z) :=
    ⟨by rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, ← Category.assoc, sq.w]; rfl⟩
  have heq : sq'.lift ≫ PointedObject.homRestriction Y Z =
      sq'.lift ≫ PointedObject.homConstant Y Z := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_restriction i Z, ← Category.assoc, sq'.fac_right,
      Category.assoc, PointedObject.basedHomι_condition]
    dsimp only [PointedObject.homConstant]
    rfl
  let l : B ⟶ (PointedObject.basedHom Y Z).right :=
    equalizer.lift (f := PointedObject.homRestriction Y Z)
      (g := PointedObject.homConstant Y Z) sq'.lift heq
  have hl : l ≫ PointedObject.basedHomι Y Z = sq'.lift := equalizer.lift_ι ..
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply (cancel_mono (PointedObject.basedHomι Y Z)).mp
    rw [Category.assoc, hl]
    exact sq'.fac_left
  · apply (cancel_mono (PointedObject.basedHomι X Z)).mp
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, ← Category.assoc, hl]
    exact sq'.fac_right

/-- 概要：単射に沿う点つき写像空間の制限は Kan fibration。
方針：Mathlib の指数版 pushout-product の相対充填を等化子へ戻す。
規約：Ω 条件も源の Kan 性も使わない。
使われ方：BF 1978 §2、HTT A.3.3。Hom の塔の遷移。 -/
theorem pre_fibration {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    [Mono i.right] (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Z) := by
  rw [fibration_iff]
  intro A B j hj
  have : HasLiftingProperty j ((MonoidalClosed.pre i.right).app Z.right) := by
    have h := (SSet.modelCategoryQuillen.fibration_iff
      ((MonoidalClosed.pre i.right).app Z.right)).mp inferInstance
    exact h j hj
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_hasLiftingProperty i Z j

end

end PointedMapping

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.basedHom_kanComplex := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.basepoint_mono := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basepoint_mono

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.pre := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.pre_fibration := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.pre_hasLiftingProperty := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_hasLiftingProperty

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.pre_restriction := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_restriction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.pre_restriction_assoc := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_restriction_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.pre_ι := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.pre_ι_assoc := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.restriction_fibration := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.restriction_fibration

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.pre._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.pre._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.pre._proof_3 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre._proof_3
