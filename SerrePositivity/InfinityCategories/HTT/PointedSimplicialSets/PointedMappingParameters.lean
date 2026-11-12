module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
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
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import SerrePositivity.Spectra.Pointed.InternalHom
public import SerrePositivity.Spectra.Pointed.SmashCurrying
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
分割で生成：docstring を書き直すこと
概要：任意の単体集合をパラメータとする点つき写像族の curry。
方針：源の基点上の定数性を内部 Hom の等化子条件へ移す。
規約：パラメータ自体に基点は要求しない。
使われ方：Goerss–Jardine I §7、HTT A.3.3。path space の収縮の構成。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory

namespace SerrePositivity.KST.Spectra.PointedMapping
end SerrePositivity.KST.Spectra.PointedMapping
namespace SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets
open _root_.SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y : PointedSimplicialSet.{u}) {A : SSet.{u}}

/-- 概要：源の基点で定数の写像族を点つき Hom への射へ移す。
方針：通常の指数の curry を等化子へ持ち上げる。
規約：パラメータ A は任意の単体集合。
使われ方：HTT A.3.3、Goerss–Jardine I §7。path のパラメータ付き収縮。 -/
def paramCurry (f : X.right ⊗ A ⟶ Y.right)
    (hf : X.hom ▷ A ≫ f = toUnit (𝟙_ SSet.{u} ⊗ A) ≫ Y.hom) :
    A ⟶ (PointedObject.basedHom X Y).right :=
  equalizer.lift (f := PointedObject.homRestriction X Y)
    (g := PointedObject.homConstant X Y) (MonoidalClosed.curry f) (by
      rw [PointedObject.homRestriction, MonoidalClosed.curry_pre_app, hf,
        PointedObject.curry_constant]
      dsimp only [PointedObject.homConstant, PointedObject.homBasepoint, PointedObject.point]
      simp only [comp_toUnit_assoc]
      rfl)

/-- 概要：パラメータ付き curry の包含後の射は通常の curry。
方針：等化子への持ち上げの計算則を使う。
規約：基点条件の証明の選択に依存しない。
使われ方：HTT A.3.3。評価と端点の検査。 -/
@[reassoc (attr := simp)]
theorem paramCurry_ι (f : X.right ⊗ A ⟶ Y.right)
    (hf : X.hom ▷ A ≫ f = toUnit (𝟙_ SSet.{u} ⊗ A) ≫ Y.hom) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry X Y f hf ≫ PointedObject.basedHomι X Y = MonoidalClosed.curry f :=
  equalizer.lift_ι ..

/-- 概要：点つき Hom への任意のパラメータ付き射の uncurry は源の基点で定数。
方針：等化子条件を指数の随伴で移す。
規約：A に基点や Kan 性は要求しない。
使われ方：Goerss–Jardine I §7、HTT A.3.3。path space の評価。 -/
theorem uncurry_basepoint (f : A ⟶ (PointedObject.basedHom X Y).right) :
    X.hom ▷ A ≫ MonoidalClosed.uncurry (f ≫ PointedObject.basedHomι X Y) =
      toUnit (𝟙_ SSet.{u} ⊗ A) ≫ Y.hom := by
  apply MonoidalClosed.curry_injective
  rw [← MonoidalClosed.curry_pre_app, MonoidalClosed.curry_uncurry]
  change f ≫ PointedObject.basedHomι X Y ≫ PointedObject.homRestriction X Y = _
  rw [PointedObject.basedHomι_condition]
  dsimp only [PointedObject.homConstant, PointedObject.homBasepoint, PointedObject.point]
  conv_rhs => rw [PointedObject.curry_constant]
  simp only [comp_toUnit_assoc]
  rfl

end

end SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.paramCurry := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.paramCurry_ι := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.paramCurry_ι_assoc := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.uncurry_basepoint := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.paramCurry._proof_1 := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.paramCurry._proof_2 := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.PointedMapping.paramCurry.congr_simp := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry.congr_simp
