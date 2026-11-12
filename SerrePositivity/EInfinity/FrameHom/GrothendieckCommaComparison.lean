module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.GrothendieckCommaTransport
public import SerrePositivity.EInfinity.FrameHom.ThomasonNaturality
public import SerrePositivity.EInfinity.FrameHom.CommaNerveBarProjection

/-!
# comma 全図式の忘却と元の移送の比較

概要：comma 全図式の忘却から、元の移送による全図式の比較への自然変換を作る。
方針：元の各脚の移送射を使い、Thomason 射の後の忘却を同じ bar 射影と照合。
規約：同じ宇宙の小圏。元の脚と全射を保持し、追加の比較を仮定しない。
使われ方：comma bar の射影の反転性を元の Thomason 射の反転性へ移す。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.EInfinity.FrameHom.Thomason
open SerrePositivity.SimplicialModel

variable {D : Type u} [Category.{u} D] (G : D ⥤ Cat.{u, u})

/-- 元の comma 全図式の対象から同じ元の全図式の対象を取り出す。 -/
def commaTotalForget : Grothendieck (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaDiagram G) ⥤ Grothendieck G where
  obj S := S.fiber.left
  map f := f.fiber.left
  map_id S := by
    change (Grothendieck.id S).fiber.left = 𝟙 S.fiber.left
    dsimp only [Grothendieck.id]
    rw [CostructuredArrow.eqToHom_left]
    rfl
  map_comp f g := by
    change (f ≫ g).fiber.left = f.fiber.left ≫ g.fiber.left
    rw [Grothendieck.comp_fiber, CostructuredArrow.comp_left,
      CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
    exact Category.id_comp _

/-- 同じ元の脚に沿う移送射が、忘却から元の全図式の比較への自然変換を与える。 -/
def commaTotalTransport : commaTotalForget G ⟶
    Grothendieck.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportComparison G) where
  app S := Grothendieck.toTransport S.fiber.left S.fiber.hom
  naturality {S T} f := by
    refine Grothendieck.ext _ _ (by
      change f.fiber.left.base ≫ T.fiber.hom = S.fiber.hom ≫ f.base
      exact CostructuredArrow.w f.fiber) ?_
    dsimp only [commaTotalForget, Functor.comp_map, Grothendieck.toTransport,
      Grothendieck.map, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportComparison, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transport]
    simp only [Grothendieck.comp_fiber, CategoryTheory.Functor.map_id, Cat.eqToHom_app,
      Category.id_comp, Category.comp_id, eqToHom_trans_assoc]
    dsimp only [Functor.toCatHom_toFunctor]
    simp only [eqToHom_trans_assoc]

/-- 同じ宇宙の ULift の単体と元の単体の明示的な同型。 -/
def selfLiftIso (K : SSet.{u}) : SSet.uliftFunctor.{u, u}.obj K ≅ K where
  hom := { app _ := ↾ULift.down, naturality _ _ _ := rfl }
  inv := { app _ := ↾ULift.up, naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- 元の comma 射列の Thomason 単体の忘却は、最初の元のラベルの射列。 -/
lemma commaSimplex_forget {n : ℕ} (c : ComposableArrows (values (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaDiagram G) n).Elements n) :
    simplex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaDiagram G) c ⋙ commaTotalForget G =
      CommaNerve.chain (Grothendieck.forget G) n (c.obj 0) := by
  rw [← LabelledChain.reconstruct (values (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaDiagram G) n) c]
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  dsimp only [Functor.comp_map, commaTotalForget, simplex]
  rw [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
  simp only [eqToHom_refl, Category.id_comp]
  rfl

/-- 同じ Thomason 射の後の忘却は、既存の元の comma bar 射影そのもの。 -/
lemma commaMap_forget :
    map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaDiagram G) ≫ nerveMap (commaTotalForget G) =
      CommaNerve.barProjection (Grothendieck.forget G) ≫
        (selfLiftIso (nerve (Grothendieck G))).hom := by
  ext n c
  exact commaSimplex_forget G c

/-- 同じ comma の比較合成は、元の bar 射影の反転性から反転される。 -/
lemma commaMap_forget_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaDiagram G) ≫ nerveMap (commaTotalForget G))) := by
  have := CommaNerve.barProjection_localized_isIso (Grothendieck.forget G)
  rw [commaMap_forget, CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.EInfinity.FrameHom.Thomason
