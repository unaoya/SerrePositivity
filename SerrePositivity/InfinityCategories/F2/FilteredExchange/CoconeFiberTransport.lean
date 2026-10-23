module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeFiberEvaluation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantDiagramTransportComparison

/-!
概要：元の余錐の全 Hom の相対合成を、元の fiber 写像に対する普遍輸送の評価と比較する。
方針：定値図式の作用の輸送比較を第一の相対評価で制限し、直積座標の往復を消去する。
規約：元の余錐・全 Hom の族・底を保持する。
使われ方：全空間の単位の前合成との整合性への fiber 側の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 概要：元の全 Hom の相対合成の評価は元の余錐の fiber 写像の普遍輸送と同型。
方針：全族の輸送比較で相対合成の第二因子を移し、第一因子の二座標を簡約する。
規約：元の全 Hom を保持する。使われ方：単位の写像による前合成との比較。 -/
def coconeFiberTransportIso (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌) :
    FunctorIso
      (uncurry (coconePointHomRelativeComposite c z ≫
        (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom))
      (lift (fst (leftUnstraightening F) (pinchedHomLeft c.vertex z) ≫ coconeFiberMap c)
        (snd (leftUnstraightening F) (pinchedHomLeft c.vertex z)) ≫
          (pointedIntervalTransport
            (pinchedHomLeftToIntervalMappingSpace c.vertex z)).endpoint) := by
  let E := leftUnstraightening F
  let T := pinchedHomLeft c.vertex z
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
  have e := (constantDiagramMappingTransportIso B
    (pinchedHomLeftToIntervalMappingSpace c.vertex z)).precomp S
  have hleft : uncurry (coconePointHomRelativeComposite c z ≫
      (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom) =
        S ≫ uncurry ((coconePointHomSecondTransformation c z ≫
          leftUnstraighteningMappingSpaceMap (SSet.const c.vertex) (SSet.const z : B ⟶ _)) ≫
            (constantUnstraighteningRelativeIso
              (leftUnstraighteningProjection (SSet.const c.vertex : B ⟶ _)) z).hom) :=
    coconePointHomRelativeComposite_coordinates c z
  change FunctorIso (S ≫ _) (S ≫ (constantUnstraighteningFiberProjection B c.vertex ▷ T) ≫
    (pointedIntervalTransport (pinchedHomLeftToIntervalMappingSpace c.vertex z)).endpoint) at e
  rw [← Category.assoc, hS] at e
  exact Eq.mpr (congrArg (fun q : E ⊗ T ⟶ vertexFiber pointedSpaceProjection z ↦
    FunctorIso q (lift (fst E T ≫ coconeFiberMap c) (snd E T) ≫
      (pointedIntervalTransport
        (pinchedHomLeftToIntervalMappingSpace c.vertex z)).endpoint)) hleft) e

end SerrePositivity.InfinityCategories.F2
