module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteLocalEquivalenceLocalHom
public import SerrePositivity.InfinityCategories.Sheaves.SheafEquivalence
public import SerrePositivity.InfinityCategories.Sheaves.Sheafify
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveInvertedHom

/-!
概要：指定した層化の反射は、集合値局所同値の離散表示の射を反転する。
方針：局所頂点の層条件を単位の同型から得て、写像空間の局所性の判定に入れる。
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
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Truncated.HomotopyCategory

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 指定した層化の反射は、集合値局所同値の離散表示の射を反転する。 -/
@[cite HTT "6.2.2.7" (partial := special) "小さい通常の site の離散前層の層化の比較。"]
lemma discreteLocalEquiv_reflector_map_isIso :
∀ {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
 (hJ : Sheafification J SpaceInfinity.{u}) {P Q : Cᵒᵖ ⥤ Type u}
 (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ),
 IsIso ((hoFunctor.map (Classical.choice hJ).reflector).toFunctor.map
 (discretePresheafHom φ)) := by
  intro C hC J hJ P Q φ hφ
  let r := Classical.choice hJ
  apply (reflective_isIso_map_iff_localHom r (discretePresheafHom φ)).mpr
  intro z hz
  let η := qcatUnitComponent r.unit z
  letI : IsIso η := hz
  have hZ : sheafProperty J z :=
    (sheafProperty_iff_of_vertexIso J (asIso η)).mpr (r.localization_mem z)
  let O := vertexToPresheaf z
  have hO : IsSheaf J O := hZ
  have hv : functorVertex O = z := (functorVertexEquiv _ _).apply_symm_apply z
  rw [← hv]
  exact discreteHom_isLocalForHom_of_localEquiv J φ hφ O hO

end SerrePositivity.InfinityCategories.Sheaves
