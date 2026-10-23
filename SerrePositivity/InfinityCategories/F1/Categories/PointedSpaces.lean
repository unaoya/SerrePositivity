module

public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity

/-!
概要：空間の ∞ 圏の頂点と pointed space の射影。
方針：Kan 複体を定値豊穣関手で頂点にし、Δ⁰ の頂点からの coslice を取る。
規約：𝒮 の定義は coherent nerve のまま使用する。
使われ方：Kerodon Construction 5.5.2.1、Proposition 5.5.2.2、left unstraightening の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：Kan 複体を coherent nerve で定義した 𝒮 の頂点として表す。
方針：対象を固定し全 Hom を恒等へ送る豊穣関手を作る。
規約：単体的圏 KanObject の対象 K を入力する。
使われ方：Kerodon Construction 3.1.6.1、pointed space の始点 Δ⁰ の指定。 -/
noncomputable def spaceInfinityVertex (K : KanObject.{u}) : SpaceInfinity.{u} _⦋0⦌ where
  obj _ := K
  map _ _ := SSet.const (functorVertex (𝟙 K.obj))
  map_id _ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  map_comp _ _ _ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl

/-- 概要：pointed space の始点に使う標準零単体の Kan 複体。
方針：標準零単体の全ホーン充填性を使う。
規約：対象は宇宙 u の Δ[0]。
使われ方：Kerodon Construction 5.5.2.1、𝒮 内の一点空間。 -/
def pointKanObject : KanObject.{u} := ⟨Δ[0], by
  rw [KanComplex.iff]
  intro n i f _hf
  refine ⟨stdSimplex.isTerminalObj₀.from _, ?_⟩
  intro j hj
  exact stdSimplex.isTerminalObj₀.hom_ext _ _⟩

/-- 概要：空間の ∞ 圏での一点空間の頂点。
方針：標準零単体の Kan 複体の頂点表示を取る。
規約：𝒮 の単体の宇宙は u+1。
使われ方：Kerodon Construction 5.5.2.1、pointed space の coslice。 -/
noncomputable def pointSpaceVertex : SpaceInfinity.{u} _⦋0⦌ := spaceInfinityVertex pointKanObject.{u}

/-- 概要：pointed space の ∞ 圏。
方針：𝒮 の一点空間の頂点からの coslice を取る。
規約：厳密な点付き射だけに制限しない。
使われ方：Kerodon Construction 5.5.2.1、𝒮 値関手の unstraightening の全空間。 -/
noncomputable def PointedSpaceInfinity : SSet.{u + 1} :=
  sliceUnder (SSet.yonedaEquiv.symm pointSpaceVertex.{u})

/-- 概要：pointed space から元の空間への射影。
方針：coslice の右因子への射影を使う。
規約：値域は coherent nerve による SpaceInfinity。
使われ方：Kerodon Proposition 5.5.2.2、left unstraightening の射影。 -/
noncomputable def pointedSpaceProjection : PointedSpaceInfinity.{u} ⟶ SpaceInfinity.{u} :=
  sliceUnderProjection (SSet.yonedaEquiv.symm pointSpaceVertex.{u})

/-- 概要：pointed space の射影は left fibration。
方針：quasicategory の coslice 射影の left fibration 性を使う。
規約：追加の充填仮定を置かない。
使われ方：Kerodon Proposition 5.5.2.2、底変換での unstraightening。 -/
instance pointedSpaceProjection_leftFibration : LeftFibration pointedSpaceProjection.{u} :=
  sliceUnderProjection_leftFibration _

/-- 概要：pointed space の全空間は quasicategory。
方針：SpaceInfinity への inner fibration 性を使う。
規約：𝒮 の極限・余極限は使わない。
使われ方：Kerodon Proposition 5.5.2.2、unstraightening の出発点。 -/
instance pointedSpaceInfinity_quasicategory : Quasicategory PointedSpaceInfinity.{u} :=
  quasicategory_of_innerFibration pointedSpaceProjection

end SerrePositivity.InfinityCategories
