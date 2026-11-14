module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：空間の ∞ 圏の頂点と pointed space の射影。
方針：Kan 複体を定値豊穣関手で頂点にし、Δ⁰ の頂点からの coslice を取る。
規約：𝒮 の定義は coherent nerve のまま使用する。
使われ方：Kerodon Construction 5.5.2.1（Tag 01ZW）、Proposition 5.5.2.2（Tag 01ZX）、left unstraightening の入力。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：Kan 複体を coherent nerve で定義した 𝒮 の頂点として表す。
方針：対象を固定し全 Hom を恒等へ送る豊穣関手を作る。
規約：単体的圏 KanObject の対象 K を入力する。
使われ方：Kerodon Construction 3.1.6.1（Tag 00TZ）、pointed space の始点 Δ⁰ の指定。 -/
noncomputable def spaceInfinityVertex (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌ where
  obj _ := K
  map _ _ := SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 K.obj))
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
使われ方：Kerodon Construction 5.5.2.1（Tag 01ZW）、𝒮 内の一点空間。 -/
@[kerodon 020T]
def pointKanObject : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} := ⟨Δ[0], by
  rw [KanComplex.iff]
  intro n i f _hf
  refine ⟨stdSimplex.isTerminalObj₀.from _, ?_⟩
  intro j hj
  exact stdSimplex.isTerminalObj₀.hom_ext _ _⟩

/-- 概要：空間の ∞ 圏での一点空間の頂点。
方針：標準零単体の Kan 複体の頂点表示を取る。
規約：𝒮 の単体の宇宙は u+1。
使われ方：Kerodon Construction 5.5.2.1（Tag 01ZW）、pointed space の coslice。 -/
noncomputable def pointSpaceVertex : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌ := spaceInfinityVertex pointKanObject.{u}

/-- 概要：pointed space の ∞ 圏。
方針：𝒮 の一点空間の頂点からの coslice を取る。
規約：厳密な点付き射だけに制限しない。
使われ方：Kerodon Construction 5.5.2.1（Tag 01ZW）、𝒮 値関手の unstraightening の全空間。 -/
@[kerodon 01ZW]
noncomputable def PointedSpaceInfinity : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm pointSpaceVertex.{u})

/-- 概要：pointed space から元の空間への射影。
方針：coslice の右因子への射影を使う。
規約：値域は coherent nerve による SpaceInfinity。
使われ方：Kerodon Proposition 5.5.2.2（Tag 01ZX）、left unstraightening の射影。 -/
noncomputable def pointedSpaceProjection : PointedSpaceInfinity.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm pointSpaceVertex.{u})

/-- 概要：pointed space の射影は left fibration。
方針：quasicategory の coslice 射影の left fibration 性を使う。
規約：追加の充填仮定を置かない。
使われ方：Kerodon Proposition 5.5.2.2（Tag 01ZX）、底変換での unstraightening。 -/
@[kerodon 01ZX]
instance pointedSpaceProjection_leftFibration : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration pointedSpaceProjection.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderProjection_leftFibration _

/-- 概要：pointed space の全空間は quasicategory。
方針：SpaceInfinity への inner fibration 性を使う。
規約：𝒮 の極限・余極限は使わない。
使われ方：Kerodon Proposition 5.5.2.2（Tag 01ZX）、unstraightening の出発点。 -/
@[kerodon 01ZX]
instance pointedSpaceInfinity_quasicategory : Quasicategory PointedSpaceInfinity.{u} :=
  quasicategory_of_innerFibration pointedSpaceProjection

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.4.2.5" (partial := component) "仮定：準圏模型で空間の点を選ぶ（HA と一致）。結論：一点空間を始域とする coslice により pointed spaces を得る（Lean が弱い：有限余極限で生成される有限空間およびその pointed 部分圏をこの型で構成しない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity
attribute [cite HTT "3.3.2.8" (partial := stronger-hyp) "仮定：小さい left fibration p:X→S に加え S が準圏（Lean が強い）。結論：nativeLeftTransportRepresentation p の図式 S→SpaceInfinity の、pointSpaceVertex からの coslice の引戻しへ、底を厳密に保つ前合成同値がある（一致）。任意の単体的 S に対して同じ比較を同値とする型はない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity
