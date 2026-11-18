module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteLocalEquivalenceReflector

/-!
概要：層化関手は、集合値局所同値を表す元の離散前層の辺を反転する。
方針：反射の結果を充満包含で写し、両端の型移送を除く。
  文献対応：HTT 6.2.2.7、通常の小さい site の集合値前層の場合。
使われ方：離散前層の層化の指定比較。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open Truncated.HomotopyCategory

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 層化関手は、集合値局所同値を表す元の離散前層の辺を反転する。 -/
@[cite HTT "6.2.2.7" (partial := special) "小さい通常の site の離散前層の層化の比較。"]
lemma localEquiv_of_sheafifyIso :
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
  {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ),
  IsInvertibleEdge ((nerve.edgeMk φ).map
    ((discretePresheafInclusion C).val ≫ sheafificationFunctor J hJ)).toTruncated := by
  intro C hC J hJ P Q φ hφ
  let r := Classical.choice hJ
  let L := sheafificationFunctor J hJ
  let i := (fullSubcomplexOnVertices (PresheafCat C SpaceInfinity.{u}) (sheafProperty J)).ι
  let f := discretePresheafHom φ
  letI : IsIso ((hoFunctor.map r.reflector).toFunctor.map f) :=
    discreteLocalEquiv_reflector_map_isIso J hJ φ hφ
  have hL : IsIso ((hoFunctor.map L).toFunctor.map f) := by
    change IsIso ((hoFunctor.map (r.reflector ≫ i)).toFunctor.map f)
    rw [Functor.map_comp]
    exact inferInstanceAs (IsIso ((hoFunctor.map i).toFunctor.map
      ((hoFunctor.map r.reflector).toFunctor.map f)))
  let e := ((nerve.edgeMk φ).map (discretePresheafInclusion C).val).toTruncated
  have h := discretePresheafHom_eq_normalized φ
  change IsIso ((hoFunctor.map L).toFunctor.map (discretePresheafHom φ)) at hL
  rw [h] at hL
  simp only [Functor.map_comp, isIso_comp_left_iff,
    isIso_comp_right_iff] at hL
  have he : IsIso ((hoFunctor.map L).toFunctor.map (homMk e)) := hL
  exact he

end SerrePositivity.InfinityCategories.Sheaves
