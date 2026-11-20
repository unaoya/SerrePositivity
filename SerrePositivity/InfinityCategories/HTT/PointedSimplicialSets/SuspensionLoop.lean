module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
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
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.Spectra.Pointed.Basic
public import SerrePositivity.Spectra.Pointed.InternalHom
public import SerrePositivity.Spectra.Pointed.Smash
public import SerrePositivity.Spectra.Pointed.SmashMonoidal
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic
public import SerrePositivity.Spectra.PointedSimplicialSet.InternalHom
public import SerrePositivity.Spectra.PointedSimplicialSet.Spheres

/-!
分割で生成：docstring を書き直すこと
概要：点つき Kan 複体の suspension と loop の随伴。
方針：単体的円との smash と点つき内部 Hom の実構成を借りる。
規約：モデル構造を用いず、loop の Kan 性は相対ホーン充填で証明する。
使われ方：HA §1.4.2、BF 1978 §2、HTT A.3.3。Ω スペクトルの構造。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき単体集合の reduced suspension。
方針：単体的円 Δ[1]/∂Δ[1] との smash を取る。
規約：この単体集合自体の Kan 性は要求しない。
使われ方：BF 1978 §2、HA §1.4.2。スペクトルの構造写像の定義域。 -/
abbrev suspension (X : PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  PointedSimplicialSet.circle ⊗ X

/-- 概要：点つき単体集合の loop 対象。
方針：単体的円からの点つき内部 Hom を取る。
規約：基点は定数ループ。
使われ方：HA §1.4.2、BF 1978 §2。Ω 条件の標的。 -/
abbrev loopSpace (X : PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  PointedObject.basedHom PointedSimplicialSet.circle X

/-- 概要：suspension と loop の間の随伴の Hom 同値。
方針：smash と点つき内部 Hom の構成済み随伴を使う。
規約：通常の点つき射の同値。
使われ方：HA §1.4.2、BF 1978 §2。構造写像の随伴。 -/
def suspensionLoopEquiv (X Y : PointedSimplicialSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X ⟶ Y) ≃ (X ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) :=
  (PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle).homEquiv X Y

end

end SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
