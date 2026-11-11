module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeWeightAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightMapMono
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
概要：終対象の頂点から圏の nerve への包含は anodyne。
方針：一点順序圏から終対象への定数関手が終対象を保つ単射であることを使う。
規約：nerve の Kan 性や、向きを反転した単一ホモトピーを仮定しない。
使われ方：Goerss–Jardine VII §4。終頂点射の各段の導来写像空間による比較。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet

open SerrePositivity.InfinityCategories
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.NerveTerminalPoint
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 一点順序圏の唯一の対象は終対象。 -/
def unitTerminal : IsTerminal (ULift.up (0 : Fin 1) : ULift.{u} (Fin 1)) :=
  IsTerminal.ofUniqueHom (fun x ↦ homOfLE (by
    change x.down ≤ (0 : Fin 1)
    exact Fin.le_last x.down)) (fun _ _ ↦ Subsingleton.elim _ _)

/-- 一点順序圏を指定対象へ送る定数関手。 -/
def pointFunctor {C : Type u} [SmallCategory C] (c : C) : ULift.{u} (Fin 1) ⥤ C :=
  (Functor.const _).obj c

/-- 終対象の頂点を標準零単体から nerve に含める射。 -/
def inclusion {C : Type u} [SmallCategory C] (c : C) : (Δ[0] : SSet.{u}) ⟶ nerve C :=
  (stdSimplex.isoNerve 0).hom ≫ nerveMap (pointFunctor c)

/-- 終対象の頂点の包含は実際の anodyne 射。 -/
lemma anodyne {C : Type u} [SmallCategory C] {c : C} (hc : IsTerminal c) :
    anodyneExtensions (inclusion c) := by
  let F := pointFunctor c
  let : F.Faithful :=
    { map_injective := fun {a b} f g _ ↦ Subsingleton.elim f g }
  let : Mono (nerveMap F) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveMap_mono_of_faithful F
    (fun _ _ _ ↦ Subsingleton.elim _ _)
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (nerveMap F) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveMap_preservingTerminal_rightAnodyne F unitTerminal hc
  exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.anodyne_of_rightAnodyne _ hF)

end
end SerrePositivity.KST.Spectra.NerveTerminalPoint
