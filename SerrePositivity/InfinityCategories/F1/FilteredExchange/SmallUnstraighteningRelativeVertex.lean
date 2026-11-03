module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverIsomorphism
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningMappingSpace
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningOverMap
public import SerrePositivity.InfinityCategories.F1.Universe.RelativeFunctor
public import SerrePositivity.InfinityCategories.PinchedHom.Basic
public import SerrePositivity.InfinityCategories.F1.UniverseVertexIso

/-!
概要：元の底上の射の相対頂点を小さい全空間の相対写像空間へ移す。
方針：相対内部 Hom の縮小同型の頂点を、底上の縮小の自然性で計算する。
規約：底を固定したまま移送。使われ方：元の cospan の可換円柱を底上で保持。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：相対写像空間の縮小同型の逆は元の底上の射を元の小さい相対頂点へ移す。
方針：順方向の頂点を計算し、同型の往復で戻す。
規約：元の射と底上の可換性を保持。使われ方：指定相対同型の下降。 -/
lemma smallUnstraighteningRelativeIso_inv_vertex {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : leftUnstraightening F ⟶ leftUnstraightening G)
    (hf : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F) :
    (smallLeftUnstraighteningRelativeFunctorIso F G).inv.app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
        f hf) =
      ULift.up.{u + 1, u}
        (relativeFunctorVertex (smallLeftUnstraighteningProjection G)
          (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningOverMap F G f)
          (smallLeftUnstraighteningOverMap_projection F G f hf)) := by
  let s := smallLeftUnstraighteningOverMap F G f
  have hs : s ≫ smallLeftUnstraighteningProjection G = smallLeftUnstraighteningProjection F :=
    smallLeftUnstraighteningOverMap_projection F G f hf
  let v := relativeFunctorVertex (smallLeftUnstraighteningProjection G)
    (smallLeftUnstraighteningProjection F) s hs
  have hv : (smallLeftUnstraighteningRelativeFunctorIso F G).hom.app (Opposite.op ⦋0⦌)
      (ULift.up v) = relativeFunctorVertex (leftUnstraighteningProjection G)
        (leftUnstraighteningProjection F) f hf := by
    change (relativeFunctorOverIso (smallLeftUnstraighteningOverIso F)
      (smallLeftUnstraighteningOverIso G)).hom.app (Opposite.op ⦋0⦌)
        ((uliftRelativeFunctorIso (smallLeftUnstraighteningProjection G)
          (smallLeftUnstraighteningProjection F)).hom.app (Opposite.op ⦋0⦌) (ULift.up v)) = _
    have h₀ : (uliftRelativeFunctorIso (smallLeftUnstraighteningProjection G)
        (smallLeftUnstraighteningProjection F)).hom.app (Opposite.op ⦋0⦌) (ULift.up v) =
        relativeFunctorVertex
          ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection G))
          ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection F))
          ((SSet.uliftFunctor.{u + 1, u}).map s)
          (by rw [← Functor.map_comp, hs]) := rfl
    rw [h₀]
    refine (relativeFunctorOverIso_vertex (smallLeftUnstraighteningOverIso F)
      (smallLeftUnstraighteningOverIso G) ((SSet.uliftFunctor.{u + 1, u}).map s)
      (by
        change (SSet.uliftFunctor.{u + 1, u}).map s ≫
          (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection G) = _
        rw [← Functor.map_comp, hs]
        rfl)).trans ?_
    apply Subtype.ext
    apply congrArg functorVertex
    change ((smallLeftUnstraighteningIso F).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map s) ≫ (smallLeftUnstraighteningIso G).hom = f
    dsimp only [s]
    rw [Category.assoc, smallLeftUnstraighteningOverMap_naturality]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [← hv]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (smallLeftUnstraighteningRelativeFunctorIso F G).hom_inv_id
      (Opposite.op ⦋0⦌)) _

/-- 概要：元の底上の二射の指定相対同型を元の小さい相対写像空間へ降ろす。
方針：相対内部 Hom の同型の逆と頂点同型の下降。
規約：底を固定したまま移送。使われ方：元の二三角形の指定相対可換性。 -/
def smallUnstraighteningRelativeVertexIso {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    {f g : leftUnstraightening F ⟶ leftUnstraightening G}
    (hf : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
    (hg : g ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
    (e : VertexIso (relativeFunctorVertex _ _ f hf) (relativeFunctorVertex _ _ g hg)) :
    VertexIso
      (relativeFunctorVertex _ _ (smallLeftUnstraighteningOverMap F G f)
        (smallLeftUnstraighteningOverMap_projection F G f hf))
      (relativeFunctorVertex _ _ (smallLeftUnstraighteningOverMap F G g)
        (smallLeftUnstraighteningOverMap_projection F G g hg)) := by
  let h := downVertexIso (e.map (smallLeftUnstraighteningRelativeFunctorIso F G).inv)
  have hs := congrArg ULift.down (smallUnstraighteningRelativeIso_inv_vertex F G f hf)
  have ht := congrArg ULift.down (smallUnstraighteningRelativeIso_inv_vertex F G g hg)
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk hs)).symm ≪≫ h ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk ht)

end SerrePositivity.InfinityCategories.F2
