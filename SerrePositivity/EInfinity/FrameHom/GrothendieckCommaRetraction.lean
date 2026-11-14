module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.GrothendieckCommaTransport
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# 各 comma 圏から元の fiber への移送の反転性

概要：元の fiber を恒等脚で戻す包含と収縮を作り、移送の nerve を反転する。
方針：各脚の元の移送射を単位に使い、同じ恒等・合成則で可換性を照合する。
規約：同じ宇宙の小圏。fiber の包含の底に関する自然性は仮定しない。
使われ方：comma 図式から元の図式への bar の比較の成分不変性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.EInfinity.FrameHom.Thomason
open SerrePositivity.SimplicialModel

variable {D : Type u} [Category.{u} D] (G : D ⥤ Cat.{u, u}) (d : D)

/-- 元の fiber の対象を同じ恒等脚の comma 対象へ戻す。 -/
def fiberIntoComma : G.obj d ⥤ CostructuredArrow (Grothendieck.forget G) d where
  obj x := ⟨⟨d, x⟩, ⟨⟨⟩⟩, 𝟙 d⟩
  map f := CostructuredArrow.homMk ((Grothendieck.ι G d).map f) (by
    change 𝟙 d ≫ 𝟙 d = 𝟙 d
    exact Category.id_comp _)
  map_id x := by
    apply CostructuredArrow.hom_ext
    exact (Grothendieck.ι G d).map_id x
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact (Grothendieck.ι G d).map_comp f g

/-- 同じ恒等脚で戻して移送すると、元の fiber の恒等関手。 -/
lemma fiberIntoComma_transport : fiberIntoComma G d ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transport G d = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun x => ?_) ?_
  · change (G.map (𝟙 d)).toFunctor.obj x = x
    rw [G.map_id]
    rfl
  · intro x y f
    change eqToHom _ ≫ (G.map (𝟙 d)).toFunctor.map (eqToHom _ ≫ f) =
      eqToHom _ ≫ f ≫ eqToHom _
    simp only [CategoryTheory.Functor.map_comp, eqToHom_map]
    rw [CategoryTheory.Functor.congr_hom congr($(G.map_id d).toFunctor)]
    simp only [Functor.id_map, Cat.Hom.id_toFunctor, eqToHom_trans_assoc]

/-- 元の脚に沿う移送射で、各 comma 対象を fiber の像へ送る単位。 -/
def transportUnit : 𝟭 (CostructuredArrow (Grothendieck.forget G) d) ⟶
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transport G d ⋙ fiberIntoComma G d where
  app S := CostructuredArrow.homMk (Grothendieck.toTransport S.left S.hom) (by
    change S.hom ≫ 𝟙 d = S.hom
    exact Category.comp_id _)
  naturality {S T} f := by
    apply CostructuredArrow.hom_ext
    simp only [CostructuredArrow.comp_left]
    refine Grothendieck.ext _ _ (by
      change f.left.base ≫ T.hom = S.hom ≫ 𝟙 d
      rw [Category.comp_id]
      exact CostructuredArrow.w f) ?_
    dsimp only [Functor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transport, fiberIntoComma, Grothendieck.toTransport,
      Grothendieck.ι]
    simp only [CostructuredArrow.homMk_left, Grothendieck.comp_fiber, Functor.id_map,
      eqToHom_trans_assoc]
    change eqToHom _ ≫ (G.map T.hom).toFunctor.map f.left.fiber ≫ 𝟙 _ =
      eqToHom _ ≫ (G.map (𝟙 d)).toFunctor.map (𝟙 _) ≫ eqToHom _ ≫
        (G.map T.hom).toFunctor.map f.left.fiber
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
      eqToHom_trans_assoc]

/-- 元の各脚に沿う移送の nerve そのものは anodyne 局所化で可逆。 -/
lemma transport_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transport G d))) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  let e : Q.obj (nerve (CostructuredArrow (Grothendieck.forget G) d)) ≅
      Q.obj (nerve (G.obj d)) :=
    { hom := Q.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transport G d))
      inv := Q.map (nerveMap (fiberIntoComma G d))
      hom_inv_id := by
        have h := AnodyneHomotopy.map_homotopy_eq Q
          (Localization.inverts _ SSet.anodyneExtensions)
          (NerveHomotopy.homotopy (transportUnit G d))
        change Q.map (𝟙 _) = Q.map
          (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transport G d) ≫ nerveMap (fiberIntoComma G d)) at h
        rw [Q.map_comp, Q.map_id] at h
        exact h.symm
      inv_hom_id := by
        rw [← Q.map_comp]
        change Q.map (nerveMap (fiberIntoComma G d ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transport G d)) = _
        rw [fiberIntoComma_transport]
        exact Q.map_id _ }
  exact e.isIso_hom

end SerrePositivity.EInfinity.FrameHom.Thomason
