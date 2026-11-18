module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteSheafificationUnitHom
public import SerrePositivity.InfinityCategories.Sheaves.OrdinarySheafificationUnitComponent
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteLocalEquivalenceSheafification
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomPostcompPointwiseInvertible

/-!
概要：通常層化の指定単位の全射は、元の層化関手で後合成すると可逆。
方針：同じ通常層化の単位の全円柱とその頂点成分を使う。
  文献対応：HTT 6.2.2.7・5.5.4.15。
使われ方：離散係数の指定層化の全比較。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open Truncated.HomotopyCategory

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 通常層化の指定単位の全射は、元の層化関手で後合成すると可逆。 -/
@[cite HTT "6.2.2.7" (partial := special) "小さい通常の site の離散係数の指定層化単位。"]
lemma discreteSheafificationUnitHom_post_isIso :
∀ {C : Type u} [SmallCategory C]
 (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u}),
let S := presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)
let I := (discretePresheafInclusion C).val
IsIso (functorHomPostcomp I (nerveMap S ≫ I)
 (sheafificationFunctor J hJ) (discreteSheafificationUnitHom J hJ)) := by
  intro C hC J hJ S I
  let H := ordinarySheafificationUnit_postHomotopy J hJ
  let L := sheafificationFunctor J hJ
  apply functorHomPostcomp_homotopy_isIso_of_pointwise H L
  intro v
  let P := nerveEquiv v
  have hv : nerveVertex P = v := nerveEquiv.left_inv v
  rw [← hv]
  let φ := CategoryTheory.toSheafify J P
  let a := (simplicialHomotopyVertexEdge H (nerveVertex P)).toTruncated.map ((truncation 2).map L)
  let b := ((nerve.edgeMk φ).map (I ≫ L)).toTruncated
  have hab : a.edge = b.edge := by
    change L.app _ (simplicialHomotopyVertexEdge H (nerveVertex P)).edge =
      L.app _ ((nerve.edgeMk φ).map I).edge
    exact congrArg (L.app _) (ordinarySheafificationUnit_postHomotopy_component J hJ P)
  exact (isInvertibleEdge_congr hab).mpr
    (localEquiv_of_sheafifyIso J hJ φ (isLocalEquivSet_toSheafify J P))

end SerrePositivity.InfinityCategories.Sheaves
