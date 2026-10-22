module

public import SerrePositivity.InfinityCategories.F2.SmallRelativeFunctorForget
public import SerrePositivity.InfinityCategories.F2.SmallUnstraighteningFunctorIsoImage
public import SerrePositivity.InfinityCategories.F2.SmallRelativeVertexIsoPresentation
public import SerrePositivity.InfinityCategories.F2.DownVertexIsoComparison

/-!
概要：小さい相対比較を忘却した指定値と、元の全空間比較を縮小した指定値を照合する。
方針：元の縮小の全族の式と、同じ頂点同型の下降の自然性を合成する。
規約：指定値・底上の条件を保持。使われ方：元の小さい三角形比較の全空間表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  {f g : leftUnstraightening F ⟶ leftUnstraightening G}
  (hf : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
  (hg : g ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
  (e : VertexIso (relativeFunctorVertex _ _ f hf) (relativeFunctorVertex _ _ g hg))
local notation "i₀" => vertexFiberι
  (CategoryTheory.Functor.map (ihom (smallLeftUnstraightening F))
    (smallLeftUnstraighteningProjection G)) (functorVertex (smallLeftUnstraighteningProjection F))
local notation "i₁" => vertexFiberι
  (CategoryTheory.Functor.map (ihom (leftUnstraightening F))
    (leftUnstraighteningProjection G)) (functorVertex (leftUnstraighteningProjection F))
local notation "p" => Iso.hom (smallLeftUnstraighteningIso F)
local notation "q" => Iso.inv (smallLeftUnstraighteningIso G)

/-- 忘却した元の小さい相対比較は、同じ元の全空間比較を縮小した指定値に一致する。 -/
lemma smallRelativeVertexIso_forget_heq_smallFunctor :
    HEq (VertexIso.map (smallUnstraighteningRelativeVertexIso F G hf hg e) i₀)
      (smallUnstraighteningFunctorIso F G (VertexIso.map e i₁)) := by
  let K := (pre p).app (leftUnstraightening G) ≫
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening F))).map q
  let U := (uliftFunctorSpaceIso.{u, u + 1}
    (smallLeftUnstraightening F) (smallLeftUnstraightening G)).inv
  have hm := vertexIso_map_heq_of_heq (smallUnstraighteningRelativeVertexIso F G hf hg e)
    (downVertexIso (VertexIso.map e (smallLeftUnstraighteningRelativeFunctorIso F G).inv))
    (congrArg ULift.down (smallUnstraighteningRelativeIso_inv_vertex F G f hf)).symm
    (congrArg ULift.down (smallUnstraighteningRelativeIso_inv_vertex F G g hg)).symm
    (smallRelativeVertexIso_heq_down_map F G hf hg e) i₀
  have hp := downVertexIso_map_comp_heq e
    (smallLeftUnstraighteningRelativeFunctorIso F G).inv
    ((SSet.uliftFunctor.{u + 1, u}).map i₀) i₁ (K ≫ U)
    (by simpa only [K, U, Category.assoc] using smallUnstraighteningRelativeIso_inv_forget F G)
  exact (hm.trans ((heq_of_eq (downVertexIso_map _ i₀)).trans hp)).trans
    (smallUnstraighteningFunctorIso_heq_down_image F G (VertexIso.map e i₁)).symm

end SerrePositivity.InfinityCategories.F2
