module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberUnit

/-!
概要：元のfiber包含は通常のGrothendieck包含をnerveへ送った同じ射。
方針：元のweighted nerveの順射でprefix係数を照合し、同じ逆を消去する。
規約：fiberの包含とラベルを別の同値へ置き換えない。
使われ方：元のnative Homのfiber射を固定始域のroofの元のラベルへ照合する。
-/
@[expose] public
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
/-- 元の順射は、通常のfiber包含を元の定値底の包含へ送る。 -/
theorem grothWeightedNerveForward_fiberInclusion (i : I) :
    nerveMap (Grothendieck.ι F i) ≫ grothWeightedNerveForward F =
      weightedNerveConstantLift (F ⋙ nerveFunctor) i := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  change (Fin (n.unop.len+1) ⥤ F.obj i) at σ
  change grothWeightedNerveSimplex F (σ ⋙ Grothendieck.ι F i) =
    ⟨_, weightedNerveConstantDiagram (F ⋙ nerveFunctor) i σ⟩
  dsimp only [grothWeightedNerveSimplex]
  refine Sigma.ext ?_ ?_
  · refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro a b f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  apply heq_of_eq
  apply NatTrans.ext
  funext k
  change (SSet.yonedaEquiv (X := nerve (F.obj i)) (n := SimplexCategory.mk k.val)).symm
    (grothWeightedPrefixFiber F (σ ⋙ Grothendieck.ι F i) k) =
      stdSimplex.map (simplexPrefixInclusion k.val n.unop.len _) ≫
        SSet.yonedaEquiv.symm σ
  rw [SSet.yonedaEquiv_symm_naturality_left]
  congr 1
  refine CategoryTheory.Functor.ext (fun j => ?_) ?_
  · change (F.map (𝟙 i)).toFunctor.obj (σ.obj (grothWeightedPrefixIndex k j)) =
      σ.obj (grothWeightedPrefixIndex k j)
    exact CategoryTheory.Functor.congr_obj congr($(F.map_id i).toFunctor) _
  · intro j l f
    simp only [grothWeightedPrefixFiber, grothWeightedPrefixArrow,
      CategoryTheory.Functor.comp_map,
      SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transport,
      Grothendieck.ι]
    change eqToHom (by
        dsimp only [CostructuredArrow.homMk_left, CostructuredArrow.mk_left,
          CostructuredArrow.mk_hom_eq_self]
        first
        | rfl
        | exact CategoryTheory.Functor.congr_obj congr($(F.map_id i).toFunctor) _
        | exact (CategoryTheory.Functor.congr_obj congr($(F.map_id i).toFunctor) _).symm) ≫
      (F.map (𝟙 i)).toFunctor.map
        (eqToHom (by
        dsimp only [CostructuredArrow.homMk_left, CostructuredArrow.mk_left,
          CostructuredArrow.mk_hom_eq_self]
        first
        | rfl
        | exact CategoryTheory.Functor.congr_obj congr($(F.map_id i).toFunctor) _
        | exact (CategoryTheory.Functor.congr_obj congr($(F.map_id i).toFunctor) _).symm) ≫ σ.map (homOfLE _)) =
      eqToHom (by
        dsimp only [CostructuredArrow.homMk_left, CostructuredArrow.mk_left,
          CostructuredArrow.mk_hom_eq_self]
        first
        | rfl
        | exact CategoryTheory.Functor.congr_obj congr($(F.map_id i).toFunctor) _
        | exact (CategoryTheory.Functor.congr_obj congr($(F.map_id i).toFunctor) _).symm) ≫ σ.map (homOfLE _) ≫
        eqToHom (by
        dsimp only [CostructuredArrow.homMk_left, CostructuredArrow.mk_left,
          CostructuredArrow.mk_hom_eq_self]
        first
        | rfl
        | exact CategoryTheory.Functor.congr_obj congr($(F.map_id i).toFunctor) _
        | exact (CategoryTheory.Functor.congr_obj congr($(F.map_id i).toFunctor) _).symm)
    rw [CategoryTheory.Functor.map_comp, eqToHom_map]
    rw [CategoryTheory.Functor.congr_hom congr($(F.map_id i).toFunctor)]
    simp only [CategoryTheory.Functor.id_map, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- 元の逆同型で定義したfiber包含は、通常のGrothendieck包含と厳密に等しい。 -/
theorem grothendieckFiberInclusion_eq_nerveMap (i : I) :
    grothendieckFiberInclusion F i = nerveMap (Grothendieck.ι F i) := by
  apply (cancel_mono (grothendieckWeightedNerveIso F).hom).mp
  rw [grothendieckFiberInclusion, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (grothWeightedNerveForward_fiberInclusion F i).symm

/-- 同じ底の通常の要素圏を、元の全要素圏へ含める通常の関手。 -/
def simplicialElementsFiberFunctor (G : I ⥤ SSet.{u}) (i : I) :
    (simplicialElementsCatDiagram G).obj i ⥤ SimplicialTotalElements G :=
  Grothendieck.ι (simplicialElementsCatDiagram G) i ⋙ simplicialElementsGrothendieckForward G

/-- 元のfiber包含は、同じ通常の要素圏の包含をnerveへ送った射そのもの。 -/
theorem simplicialElementsFiberInclusion_eq_nerveMap (G : I ⥤ SSet.{u}) (i : I) :
    simplicialElementsFiberInclusion G i = nerveMap (simplicialElementsFiberFunctor G i) := by
  rw [simplicialElementsFiberInclusion, grothendieckFiberInclusion_eq_nerveMap]
  rfl

/-- 元のfiber包含は、同じ底と元の単体次数を保持する。 -/
theorem simplicialElementsFiberFunctor_obj (G : I ⥤ SSet.{u}) (i : I)
    (s : (simplicialElementsCatDiagram G).obj i) :
    ((simplicialElementsFiberFunctor G i).obj s).obj = (i, s.obj) := rfl

/-- 元のfiber包含のラベルは、元の同じ単体のラベルそのもの。 -/
theorem simplicialElementsFiberFunctor_value (G : I ⥤ SSet.{u}) (i : I)
    (s : (simplicialElementsCatDiagram G).obj i) :
    ((simplicialElementsFiberFunctor G i).obj s).val = s.val := rfl
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
