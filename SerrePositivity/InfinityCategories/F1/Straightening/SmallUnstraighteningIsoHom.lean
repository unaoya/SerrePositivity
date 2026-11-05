module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Straightening.SmallUnstraighteningFunctorHom
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningOverMap
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingVertexRecovery

/-! # 同じ全写像空間の実比較は、可逆な指定二胞体を小さい底上の同値へ送る -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Straightening
open SerrePositivity.KST.Fibration
variable {B : SSet.{u}}
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : FunctorHom F G)

/-- 元の全写像空間で選んだ大きい射。指定二胞体の代表パラメーターを保持する。 -/
def unstraighteningFunctorHom : leftUnstraightening F ⟶ leftUnstraightening G :=
  (leftUnstraighteningMappingVertexMap F G (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomParameter a)).val

/-- 同じ大きい写像は底を厳密に保持する。 -/
theorem unstraighteningFunctorHom_projection : _root_.SerrePositivity.InfinityCategories.F1.Straightening.unstraighteningFunctorHom a ≫
    leftUnstraighteningProjection G = leftUnstraighteningProjection F :=
  (leftUnstraighteningMappingVertexMap F G (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomParameter a)).property

/-- 小さい相対写像空間からの回収式は、全空間の縮小同型による同じ共役式を与える。 -/
theorem smallUnstraighteningFunctorHom_naturality :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom a) ≫
      (smallLeftUnstraighteningIso G).hom =
      (smallLeftUnstraighteningIso F).hom ≫ _root_.SerrePositivity.InfinityCategories.F1.Straightening.unstraighteningFunctorHom a := by
  have he := _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_recover a
  change (relativeFunctorOverIso (smallLeftUnstraighteningOverIso F)
      (smallLeftUnstraighteningOverIso G)).hom.app (Opposite.op ⦋0⦌)
    ((uliftRelativeFunctorMap (smallLeftUnstraighteningProjection G)
      (smallLeftUnstraighteningProjection F)).app (Opposite.op ⦋0⦌)
        (ULift.up (relativeFunctorVertex _ _ (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom a)
          (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_projection a)))) = _ at he
  rw [uliftRelativeFunctorMap_vertex] at he
  have ht := relativeFunctorOverIso_vertex (smallLeftUnstraighteningOverIso F)
    (smallLeftUnstraighteningOverIso G)
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom a))
    (by
      change (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom a) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection G) =
          (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection F)
      rw [← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_projection])
  have hb := leftUnstraighteningMappingVertexMap_vertex F G (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomParameter a)
  have hv := ht.symm.trans (he.trans hb.symm)
  have hm : (smallLeftUnstraighteningIso F).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom a) ≫
      (smallLeftUnstraighteningIso G).hom = _root_.SerrePositivity.InfinityCategories.F1.Straightening.unstraighteningFunctorHom a := by
    have hh := functorVertex_injective (congrArg Subtype.val hv)
    change ((smallLeftUnstraighteningIso F).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom a)) ≫
      (smallLeftUnstraighteningIso G).hom = _root_.SerrePositivity.InfinityCategories.F1.Straightening.unstraighteningFunctorHom a at hh
    simpa only [Category.assoc] using hh
  have hc := congrArg (fun f => (smallLeftUnstraighteningIso F).hom ≫ f) hm
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hc

/-- 指定二胞体から作った小さい実写像は、同じ大きい実写像の縮小そのもの。 -/
theorem smallUnstraighteningFunctorHom_eq_overMap :
    _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom a =
      smallLeftUnstraighteningOverMap F G (_root_.SerrePositivity.InfinityCategories.F1.Straightening.unstraighteningFunctorHom a) := by
  apply (SSet.uliftFunctor.{u + 1, u}).map_injective
  apply (cancel_mono (smallLeftUnstraighteningIso G).hom).1
  exact (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_naturality a).trans
    (smallLeftUnstraighteningOverMap_naturality F G (_root_.SerrePositivity.InfinityCategories.F1.Straightening.unstraighteningFunctorHom a)).symm

/-- 可逆な指定二胞体の同じ代表辺は、全関手空間内でも可逆。 -/
theorem smallUnstraighteningHomEdge_isInvertible [IsIso a] :
    IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomEdge a) := by
  change IsIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomEdge a).toTruncated)
  rw [_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomEdge_hom]
  infer_instance

variable [Quasicategory B]

/-- 可逆な指定二胞体の同じ大きい実写像は前合成同値。 -/
theorem unstraighteningFunctorHom_isPrecompositionEquivalence [IsIso a] :
    IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.F1.Straightening.unstraighteningFunctorHom a) := by
  exact leftUnstraighteningMappingVertexMap_isPrecompositionEquivalence_of_isInvertibleEdge
    F G (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomEdge a) (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomEdge_isInvertible a)

/-- 可逆な指定二胞体の同じ小さい実写像も前合成同値。点の作用の回収式と同じ射を使う。 -/
theorem smallUnstraighteningFunctorHom_isPrecompositionEquivalence [IsIso a] :
    IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom a) := by
  rw [_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_eq_overMap]
  exact smallLeftUnstraighteningOverMap_isPrecompositionEquivalence F G
    (_root_.SerrePositivity.InfinityCategories.F1.Straightening.unstraighteningFunctorHom a) (_root_.SerrePositivity.InfinityCategories.F1.Straightening.unstraighteningFunctorHom_projection a)
    (_root_.SerrePositivity.InfinityCategories.F1.Straightening.unstraighteningFunctorHom_isPrecompositionEquivalence a)

end SerrePositivity.InfinityCategories.F1.Straightening

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.smallUnstraighteningFunctorHom_eq_overMap := _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_eq_overMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.smallUnstraighteningFunctorHom_isPrecompositionEquivalence := _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_isPrecompositionEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.smallUnstraighteningFunctorHom_naturality := _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningFunctorHom_naturality

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.smallUnstraighteningHomEdge_isInvertible := _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomEdge_isInvertible

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Straightening.unstraighteningFunctorHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.unstraighteningFunctorHom := _root_.SerrePositivity.InfinityCategories.F1.Straightening.unstraighteningFunctorHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.unstraighteningFunctorHom_isPrecompositionEquivalence := _root_.SerrePositivity.InfinityCategories.F1.Straightening.unstraighteningFunctorHom_isPrecompositionEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.unstraighteningFunctorHom_projection := _root_.SerrePositivity.InfinityCategories.F1.Straightening.unstraighteningFunctorHom_projection
