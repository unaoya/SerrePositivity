module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExUnit
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 全ての単体集合の細分の最終頂点写像

概要：構成済みの Ex の単位を随伴で転置し、sd(X)→X を自然に構成する。
方針：sd⊣Ex の自然な Hom 同値を使う。
規約：Moss 2020 §3 の最終頂点写像の全対象への拡張。
使われ方：二重細分の horn の境界条件を関手の射として記述する。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory

/--
概要：細分から恒等関手への自然な最終頂点写像。
方針：Ex の単位の各成分を随伴同値で転置し、自然性も同値で確認する。
規約：Moss 2020 §3。標準単体の頂点上の式で定めた単位を使う。
使われ方：二重細分からの境界写像の記述。
-/
@[kerodon 00YU]
def subdivisionLastVertexMap : SSet.sd.{u} ⟶ 𝟭 SSet.{u} where
  app X := (SSet.sdExAdjunction.homEquiv _ _).symm (exUnitAt X)
  naturality X Y f := by
    apply (SSet.sdExAdjunction.homEquiv _ _).injective
    rw [SSet.sdExAdjunction.homEquiv_naturality_left,
      SSet.sdExAdjunction.homEquiv_naturality_right]
    simpa only [Equiv.apply_symm_apply, Functor.id_obj, Functor.id_map] using exUnitAt_naturality f

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
