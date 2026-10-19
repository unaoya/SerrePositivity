module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitSpanBoundaryPath
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeBoundaryPathRectification

/-!
概要：span の普遍余錐の元の三角形が指定する境界経路を保って、元の図式の余錐を構成する。
方針：右から左への指定境界経路を右枝の制限へ持ち上げ、厳密な余錐空間の引き戻しで貼る。
規約：任意の成分の一致から経路を選ばない。使われ方：共通 path end での普遍点の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))

/-- 元の三角形から得た境界経路を、そのまま右余錐空間へ持ち上げた修正経路。 -/
def partialColimitSpecifiedBoundaryCorrection : (Δ[0] : SSet.{u + 1}) ⟶ equivalencePath
    (coconeMappingSpace (j ≫ p)
      (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).vertex) :=
  coconeBoundaryPathCorrection hp p _
    (SSet.yonedaEquiv.symm (transportedCoconeVertex dC
      (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)))
    (partialColimitSpanBoundaryPath c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
    (partialColimitSpanBoundaryPath_zero c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)

/-- 普遍 span の三角形の境界経路を指定して貼った、元の図式の固定頂点余錐の点図式。 -/
def partialColimitSpecifiedBoundaryFamily : (Δ[0] : SSet.{u + 1}) ⟶ coconeMappingSpace p
    (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).vertex := by
  apply coconeBoundaryPathRectifiedFamily hp p _
    (SSet.yonedaEquiv.symm (transportedCoconeVertex dB
      (partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)))
    (SSet.yonedaEquiv.symm (transportedCoconeVertex dC
      (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)))
    (partialColimitSpanBoundaryPath c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
    (partialColimitSpanBoundaryPath_zero c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
  simpa only [normalizedCoconeRestrictionFiber_eq, eqToHom_refl, Category.comp_id] using
    partialColimitSpanBoundaryPath_one c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC

/-- 指定した三角形の経路による貼り合わせは、左余錐の輸送像をそのまま保つ。 -/
lemma partialColimitSpecifiedBoundaryFamily_left :
    partialColimitSpecifiedBoundaryFamily hp p c hc dB dC ≫
        cosliceRestrictionFiberMap p i _ =
      SSet.yonedaEquiv.symm (transportedCoconeVertex dB
        (partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)) :=
  coconeBoundaryPathRectifiedFamily_left _ _ _ _ _ _ _ _

/-- 右余錐への制限は、元の境界経路を被覆する修正経路の反対端点。 -/
lemma partialColimitSpecifiedBoundaryFamily_right :
    partialColimitSpecifiedBoundaryFamily hp p c hc dB dC ≫
        cosliceRestrictionFiberMap p j _ =
      partialColimitSpecifiedBoundaryCorrection hp p c hc dB dC ≫ equivalencePathEndpoint _ 1 :=
  coconeBoundaryPathRectifiedFamily_right _ _ _ _ _ _ _ _

/-- 修正経路の底は、普遍 span の元の三角形から抽出した経路そのもの。 -/
lemma partialColimitSpecifiedBoundaryCorrection_projection :
    partialColimitSpecifiedBoundaryCorrection hp p c hc dB dC ≫ equivalencePathMap
        (normalizedCoconeRestrictionFiber (j ≫ p) g (coconePushoutBoundary_eq hp p) _) =
      partialColimitSpanBoundaryPath c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC :=
  coconeBoundaryPathCorrection_projection _ _ _ _ _ _

/-- 普遍 span の三角形の指定経路を保って構成した、元の coherent 図式の実際の余錐。 -/
def partialColimitSpecifiedPathCocone : JoinCocone p :=
  (SSet.yonedaEquiv (partialColimitSpecifiedBoundaryFamily hp p c hc dB dC)).val

/-- 指定経路で構成した余錐の頂点は、部分余極限 span の小さい Kan 押し出し。 -/
lemma partialColimitSpecifiedPathCocone_vertex :
    (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex = spaceInfinityVertex
      (partialColimitPushoutObject c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC) := by
  have hv := (SSet.yonedaEquiv (partialColimitSpecifiedBoundaryFamily hp p c hc dB dC)).property
  change (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex = _ at hv
  exact (hv.trans (pinchedConstant_zero _)).trans ((coherentCoconeOfDiagramEq_vertex _ _).trans
    (partialColimitPushoutCocone_vertex c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
