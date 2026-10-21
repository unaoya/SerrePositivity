module

public import SerrePositivity.InfinityCategories.F2.CoconeIntervalComposite
public import SerrePositivity.InfinityCategories.F2.ConstantDiagramTransportComparison

/-!
概要：任意の指定区間による余錐単位の合成を、その区間の普遍 fiber 輸送に比較する。
方針：定値図式の作用の全輸送比較を、元の余錐の二座標で制限する。
規約：全パラメータの関手同型。使われ方：元の単位正方形の下三角形の作用比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B T : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}
  (c : JoinCocone F) {z : SpaceInfinity.{u} _⦋0⦌}
  (a : T ⟶ intervalMappingSpace c.vertex z)

/-- 元の指定区間族による全作用は、元の余錐の fiber 写像の後の普遍輸送と同型。 -/
def coconeIntervalFiberTransportIso :
    FunctorIso (uncurry (coconeIntervalRelativeComposite c a ≫
      (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom))
      (lift (fst (leftUnstraightening F) T ≫ coconeFiberMap c) (snd _ T) ≫
        (pointedIntervalTransport a).endpoint) := by
  let E := leftUnstraightening F
  let C := leftUnstraightening (SSet.const c.vertex : B ⟶ _)
  let S : E ⊗ T ⟶ C ⊗ T :=
    lift (lift (fst E T ≫ coconeFiberMap c) (fst E T ≫ leftUnstraighteningProjection F) ≫
      (constantPullbackFiberIso pointedSpaceProjection c.vertex).inv) (snd E T)
  have hS : S ≫ (constantUnstraighteningFiberProjection B c.vertex ▷ T) =
      lift (fst E T ≫ coconeFiberMap c) (snd E T) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerRight_fst, ← Category.assoc, lift_fst]
      dsimp only [S, constantUnstraighteningFiberProjection]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, lift_fst]
    · rw [Category.assoc, whiskerRight_snd, lift_snd]
      rfl
  have e := (constantDiagramMappingTransportIso B a).precomp S
  change FunctorIso (S ≫ _) (S ≫ (constantUnstraighteningFiberProjection B c.vertex ▷ T) ≫
    (pointedIntervalTransport a).endpoint) at e
  rw [← Category.assoc, hS] at e
  have he := coconeIntervalRelativeComposite_coordinates c a
  exact Eq.mpr (congrArg (fun q : E ⊗ T ⟶ vertexFiber pointedSpaceProjection z =>
    FunctorIso q (lift (fst E T ≫ coconeFiberMap c) (snd E T) ≫
      (pointedIntervalTransport a).endpoint)) he) e

/-- 元の任意区間族の相対合成を、元の fiber 写像による前合成として全写像空間で読む。 -/
def coconeIntervalFiberHomIso :
    FunctorIso (coconeIntervalRelativeComposite c a ≫
      (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom)
      ((pointedIntervalTransport a).map ≫
        (pre (coconeFiberMap c)).app (vertexFiber pointedSpaceProjection z)) := by
  have e := (coconeIntervalFiberTransportIso c a).curry
  rw [curry_uncurry] at e
  have h : curry (lift (fst (leftUnstraightening F) T ≫ coconeFiberMap c) (snd _ T) ≫
      (pointedIntervalTransport a).endpoint) =
      (pointedIntervalTransport a).map ≫
        (pre (coconeFiberMap c)).app (vertexFiber pointedSpaceProjection z) := by
    apply uncurry_injective
    rw [uncurry_curry, uncurry_pre_app]
    change _ = (coconeFiberMap c ▷ T) ≫ uncurry (curry (pointedIntervalTransport a).endpoint)
    rw [uncurry_curry]
    rfl
  rw [h] at e
  exact e

end SerrePositivity.InfinityCategories.F2
