module
public import SerrePositivity.KST.Fibration.SmallUnstraighteningFunctorHom
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningOverMap
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingVertexRecovery

/-! # 同じ全写像空間の実比較は、可逆な指定二胞体を小さい底上の同値へ送る -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B : SSet.{u}}
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : FunctorHom F G)

/-- 元の全写像空間で選んだ大きい射。指定二胞体の代表パラメーターを保持する。 -/
def unstraighteningFunctorHom : leftUnstraightening F ⟶ leftUnstraightening G :=
  (leftUnstraighteningMappingVertexMap F G (smallUnstraighteningHomParameter a)).val

/-- 同じ大きい写像は底を厳密に保持する。 -/
theorem unstraighteningFunctorHom_projection : unstraighteningFunctorHom a ≫
    leftUnstraighteningProjection G = leftUnstraighteningProjection F :=
  (leftUnstraighteningMappingVertexMap F G (smallUnstraighteningHomParameter a)).property

/-- 小さい相対写像空間からの回収式は、全空間の縮小同型による同じ共役式を与える。 -/
theorem smallUnstraighteningFunctorHom_naturality :
    (SSet.uliftFunctor.{u + 1, u}).map (smallUnstraighteningFunctorHom a) ≫
      (smallLeftUnstraighteningIso G).hom =
      (smallLeftUnstraighteningIso F).hom ≫ unstraighteningFunctorHom a := by
  have he := smallUnstraighteningFunctorHom_recover a
  change (relativeFunctorOverIso (smallLeftUnstraighteningOverIso F)
      (smallLeftUnstraighteningOverIso G)).hom.app (Opposite.op ⦋0⦌)
    ((uliftRelativeFunctorMap (smallLeftUnstraighteningProjection G)
      (smallLeftUnstraighteningProjection F)).app (Opposite.op ⦋0⦌)
        (ULift.up (relativeFunctorVertex _ _ (smallUnstraighteningFunctorHom a)
          (smallUnstraighteningFunctorHom_projection a)))) = _ at he
  rw [uliftRelativeFunctorMap_vertex] at he
  have ht := relativeFunctorOverIso_vertex (smallLeftUnstraighteningOverIso F)
    (smallLeftUnstraighteningOverIso G)
    ((SSet.uliftFunctor.{u + 1, u}).map (smallUnstraighteningFunctorHom a))
    (by
      change (SSet.uliftFunctor.{u + 1, u}).map (smallUnstraighteningFunctorHom a) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection G) =
          (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection F)
      rw [← Functor.map_comp, smallUnstraighteningFunctorHom_projection])
  have hb := leftUnstraighteningMappingVertexMap_vertex F G (smallUnstraighteningHomParameter a)
  have hv := ht.symm.trans (he.trans hb.symm)
  have hm : (smallLeftUnstraighteningIso F).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (smallUnstraighteningFunctorHom a) ≫
      (smallLeftUnstraighteningIso G).hom = unstraighteningFunctorHom a := by
    have hh := functorVertex_injective (congrArg Subtype.val hv)
    change ((smallLeftUnstraighteningIso F).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (smallUnstraighteningFunctorHom a)) ≫
      (smallLeftUnstraighteningIso G).hom = unstraighteningFunctorHom a at hh
    simpa only [Category.assoc] using hh
  have hc := congrArg (fun f => (smallLeftUnstraighteningIso F).hom ≫ f) hm
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hc

/-- 指定二胞体から作った小さい実写像は、同じ大きい実写像の縮小そのもの。 -/
theorem smallUnstraighteningFunctorHom_eq_overMap :
    smallUnstraighteningFunctorHom a =
      smallLeftUnstraighteningOverMap F G (unstraighteningFunctorHom a) := by
  apply (SSet.uliftFunctor.{u + 1, u}).map_injective
  apply (cancel_mono (smallLeftUnstraighteningIso G).hom).1
  exact (smallUnstraighteningFunctorHom_naturality a).trans
    (smallLeftUnstraighteningOverMap_naturality F G (unstraighteningFunctorHom a)).symm

/-- 可逆な指定二胞体の同じ代表辺は、全関手空間内でも可逆。 -/
theorem smallUnstraighteningHomEdge_isInvertible [IsIso a] :
    IsInvertibleEdge (smallUnstraighteningHomEdge a) := by
  change IsIso (Truncated.HomotopyCategory.homMk (smallUnstraighteningHomEdge a).toTruncated)
  rw [smallUnstraighteningHomEdge_hom]
  infer_instance

variable [Quasicategory B]

/-- 可逆な指定二胞体の同じ大きい実写像は前合成同値。 -/
theorem unstraighteningFunctorHom_isPrecompositionEquivalence [IsIso a] :
    IsPrecompositionEquivalence (unstraighteningFunctorHom a) := by
  exact leftUnstraighteningMappingVertexMap_isPrecompositionEquivalence_of_isInvertibleEdge
    F G (smallUnstraighteningHomEdge a) (smallUnstraighteningHomEdge_isInvertible a)

/-- 可逆な指定二胞体の同じ小さい実写像も前合成同値。点の作用の回収式と同じ射を使う。 -/
theorem smallUnstraighteningFunctorHom_isPrecompositionEquivalence [IsIso a] :
    IsPrecompositionEquivalence (smallUnstraighteningFunctorHom a) := by
  rw [smallUnstraighteningFunctorHom_eq_overMap]
  exact smallLeftUnstraighteningOverMap_isPrecompositionEquivalence F G
    (unstraighteningFunctorHom a) (unstraighteningFunctorHom_projection a)
    (unstraighteningFunctorHom_isPrecompositionEquivalence a)

end SerrePositivity.KST.Fibration
