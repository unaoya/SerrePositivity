module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CoherentTerminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.EmptyCone

/-!
概要：空間の ∞ 圏の一点空間が終対象であることを証明する。
方針：一点への内部 Hom は単体集合の終対象なので、局所 Kan な圏の終対象判定を適用する。
規約：F1 の既存の KanObject・SpaceInfinity・pointSpaceVertex を使う。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、γ3c の空積の場合。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：Kan 複体から一点 Kan 複体への豊穣 Hom は単体集合の終対象。
方針：一点空間への射の一意性を curry と uncurry の同値で内部 Hom に移す。
規約：F1 の既存の豊穣構造をそのまま使う。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の空積の表現可能な条件。 -/
noncomputable def pointKanObject_sHom_isTerminal (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    IsTerminal (SimplicialCategory.sHom X _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.{u}) :=
  IsTerminal.ofUniqueHom
    (fun A ↦ curry (stdSimplex.isTerminalObj₀.from (X.obj ⊗ A)))
    (fun _ _ ↦ uncurry_injective (stdSimplex.isTerminalObj₀.hom_ext _ _))

/-- 概要：coherent nerve で定義した空間の ∞ 圏では一点空間が終対象。
方針：全ての豊穣 Hom の厳密な終対象性から、pinched Hom の可縮性を経て結論する。
規約：結論は既存の pointSpaceVertex に対する IsTerminalVertex。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB）、γ3c の空積。 -/
lemma pointSpaceVertex_isTerminalVertex : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex.{u} := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.{u})
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentNerve_isTerminalVertex_of_enrichedTerminal _ pointKanObject_sHom_isTerminal

/-- 概要：一点空間を頂点とする空間の ∞ 圏の空図式の錐。
方針：既存の一点空間に空図式の標準の錐を適用する。
規約：空図式は SpaceInfinity の空部分複体の包含。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、γ3c の空積の具体的な公開。 -/
noncomputable def spaceEmptyProductCone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (⊥ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}.Subcomplex).ι := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.emptyCone _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex.{u}

/-- 概要：空間の ∞ 圏の一点空間は空積を与える極限錐。
方針：証明した一点空間の終対象性と空図式の極限性の同値を使う。
規約：条件付きの比較界面ではなく、既存の SpaceInfinity における IsLimitCone。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB）、F2 の空積。 -/
lemma spaceEmptyProductCone_isLimitCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone spaceEmptyProductCone.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.isLimitCone_emptyCone_iff _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex.{u}).2 pointSpaceVertex_isTerminalVertex

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
