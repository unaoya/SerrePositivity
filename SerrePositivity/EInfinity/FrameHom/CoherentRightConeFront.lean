module

public import SerrePositivity.EInfinity.FrameHom.CoherentRightConeFunctor

/-!
# 元の coherent 錐の前面は元の通常図式

概要：最後の頂点を除いた制限を元の通常図式の coherent 表示へ同定する。
方針：全対象と全 Hom の定値な通常射を照合する。
規約：最後 Hom の選択は前面の式に影響しない。
使われ方：native roof prism の底の評価円柱への同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom.CoherentRightCone
open CategoryTheory SimplicialThickening SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (F : Fin (n + 1) ⥤ C) (Y : C)
  (L : ∀ i : Fin (n + 1),
    SimplicialCategory.sHom (vertex.{u} i.castSucc) (vertex (Fin.last (n + 1))) ⟶
      SimplicialCategory.sHom (F.obj i) Y)
  (hL : ∀ (i j : Fin (n + 1)) (hij : i ≤ j),
    eComp SSet (vertex.{u} i.castSucc) (vertex j.castSucc) (vertex (Fin.last (n + 1))) ≫ L i =
      lift (toUnit _ ≫ eHomEquiv SSet (F.map (homOfLE hij))) (snd _ _ ≫ L j) ≫
        eComp SSet (F.obj i) (F.obj j) Y)

lemma diagram_front :
    (SimplicialNerve C).map (PinchedHom.front n).op (diagram F Y L hL) =
      (nerveToCoherent C).app (Opposite.op ⦋n⦌) F := by
  apply EnrichedFunctor.ext SSet (fun i => obj_cast F Y i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change ((SimplicialThickening.functor (PinchedHom.front n).toOrderHom.uliftMap).map
    (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ ≫
      hom F Y L i.castSucc j.castSucc) ≫ eqToHom _ = _
  simp only [Category.assoc, hom_cast_cast]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

end SerrePositivity.EInfinity.FrameHom.CoherentRightCone
