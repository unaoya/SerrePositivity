module

public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfDerivedTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.CartesianPrismComparison

/-!
概要：元の左右導来関手の輸送を比較し、下段 cf nerve 上の自然な単位候補を構成する。
方針：右の輸送を左導来関手で引き戻して比較正方形へ代入し、零 fiber の同型で戻す。
規約：元の輸送と正方形の証人を保持し、随伴性や三角恒等式は追加の証明を要する。
使われ方：HTT 5.2.4.6、F1b の指定単位による随伴判定への入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory HomotopicalAlgebra MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] [ModelCategory C] [ModelCategory D]
  (R : EnrichedFunctor SSet.{u} D C)
  {L : C ⥤ D} (adj : L ⊣ coherentEnrichedUnderlyingFunctor R)
  [SerrePositivity.Quillen.IsLeftQuillen L]
  (fibD : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations D) (fibrations D))
  (e : EnrichedAdjunctionHomComposition R adj)
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [FixedSimplicialPushoutProduct SC.tensor] [FixedSimplicialPushoutProduct SD.tensor]


variable (cofC : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))
include fibD e SC SD cofC in
/-- 元の両輸送と比較正方形を保持した、下段 cf nerve 上の自然な単位 prism の存在。 -/
lemma quillenCfDerivedUnitPrism_exists :
    ∃ (η : (Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (CofibrantFibrantObjects C) ⟶
        SimplicialNerve (CofibrantFibrantObjects C))
      (HL : (Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (CofibrantFibrantObjects C) ⟶
        QuillenCfCollageInfinity R)
      (HR : (Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (CofibrantFibrantObjects D) ⟶
        QuillenCfCollageInfinity R)
      (J : (Δ[1] : SSet.{max u v}) ⊗
        ((Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (CofibrantFibrantObjects C)) ⟶
          QuillenCfCollageInfinity R),
      prismEndpoint 0 _ ≫ η = 𝟙 _ ∧
      prismEndpoint 1 _ ≫ η =
        quillenCfLeftDerived R adj fibD e SC SD ≫ quillenCfRightDerived R adj SC SD cofC ∧
      η ≫ quillenCfCollageBottomNerve R = prismEndpoint 0 _ ≫ J ∧
      prismEndpoint 0 _ ≫ HL = quillenCfCollageBottomNerve R ∧
      prismEndpoint 1 _ ≫ HL =
        quillenCfLeftDerived R adj fibD e SC SD ≫ quillenCfCollageTopNerve R ∧
      HL ≫ quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ ∧
      (∀ x, IsCocartesianEdge (quillenCfCollageProjection R)
        (HL.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), PinchedHom.constant x 1))) ∧
      prismEndpoint 0 _ ≫ HR =
        quillenCfRightDerived R adj SC SD cofC ≫ quillenCfCollageBottomNerve R ∧
      prismEndpoint 1 _ ≫ HR = quillenCfCollageTopNerve R ∧
      HR ≫ quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ ∧
      (∀ x, IsCartesianEdge (quillenCfCollageProjection R)
        (HR.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), PinchedHom.constant x 1))) ∧
      ((Δ[1] : SSet.{max u v}) ◁ ((boundary 1).ι ▷
        SimplicialNerve (CofibrantFibrantObjects C))) ≫ J = cartesianComparisonBoundary HL
          (((Δ[1] : SSet.{max u v}) ◁ quillenCfLeftDerived R adj fibD e SC SD) ≫ HR) ∧
      prismEndpoint 1 _ ≫ J = HL ∧
      J ≫ quillenCfCollageProjection R = ((Δ[1] : SSet.{max u v}) ◁
        fst (Δ[1] : SSet.{max u v}) _) ≫ prismFirstContraction 1 ∧
      ∀ x, IsCartesianEdge (quillenCfCollageProjection R)
        (J.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), PinchedHom.constant x 1)) := by
  let F := quillenCfLeftDerived R adj fibD e SC SD
  let G := quillenCfRightDerived R adj SC SD cofC
  obtain ⟨HL, hL0, hL1, hLp, hLc⟩ := quillenCfLeftDerived_transport R adj fibD e SC SD
  obtain ⟨HR, hR0, hR1, hRp, hRc⟩ := quillenCfRightDerived_transport R adj SC SD cofC
  let K := ((Δ[1] : SSet.{max u v}) ◁ F) ≫ HR
  have hKp : K ≫ quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ := by
    dsimp only [K]
    rw [Category.assoc, hRp]
    rfl
  have hK1 : prismEndpoint 1 _ ≫ K = prismEndpoint 1 _ ≫ HL := by
    dsimp only [K]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hR1, hL1]
  have hKc : ∀ x, IsCartesianEdge (quillenCfCollageProjection R)
      (K.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), PinchedHom.constant x 1)) := by
    intro x
    change IsCartesianEdge (quillenCfCollageProjection R)
      (HR.app (Opposite.op ⦋1⦌) (_, F.app _ (PinchedHom.constant x 1)))
    rw [pinchedConstant_map]
    exact hRc (F.app _ x)
  have := quillenCfCollageProjection_cartesianFibration R adj SC SD cofC
  obtain ⟨J, hJb, hJ1, hJp, hJc⟩ :=
    exists_cartesianPrismComparison (quillenCfCollageProjection R) HL K hLp hKp hK1 hKc
  let α := prismEndpoint 0 _ ≫ J
  have hαp : α ≫ quillenCfCollageProjection R =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
    cartesianPrismComparison_unit_base _ J hJp
  have hαb := cartesianPrismComparison_unit_boundary HL K J hJb
  have hα0 : prismEndpoint 0 _ ≫ α = quillenCfCollageBottomNerve R := by
    rw [← intervalBoundaryEndpoint_ι 0, Category.assoc, hαb,
      intervalBoundaryDiagram_zero, hL0]
  have hα1 : prismEndpoint 1 _ ≫ α = (F ≫ G) ≫ quillenCfCollageBottomNerve R := by
    rw [← intervalBoundaryEndpoint_ι 1, Category.assoc, hαb,
      intervalBoundaryDiagram_one]
    dsimp only [K]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hR0]
    rfl
  let ηf := vertexFiberLift (quillenCfCollageProjection R)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) α hαp
  let η := ηf ≫ (quillenCfBottomFiberIso R).inv
  have hηi : η ≫ quillenCfCollageBottomNerve R = α := by
    dsimp only [η]
    rw [← quillenCfBottomFiberIso_hom_ι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact vertexFiberLift_ι _ _ _ _
  have hη0 : prismEndpoint 0 _ ≫ η = 𝟙 _ := by
    apply (cancel_mono (quillenCfBottomFiberIso R).hom).mp
    apply vertexFiber_hom_ext (quillenCfCollageProjection R)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
    simp only [Category.assoc, quillenCfBottomFiberIso_hom_ι, Category.id_comp]
    rw [hηi, hα0]
  have hη1 : prismEndpoint 1 _ ≫ η = F ≫ G := by
    apply (cancel_mono (quillenCfBottomFiberIso R).hom).mp
    apply vertexFiber_hom_ext (quillenCfCollageProjection R)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
    simp only [Category.assoc, quillenCfBottomFiberIso_hom_ι]
    rw [hηi, hα1]
    exact Category.assoc _ _ _
  exact ⟨η, HL, HR, J, hη0, hη1, hηi, hL0, hL1, hLp, hLc,
    hR0, hR1, hRp, hRc, hJb, hJ1, hJp, hJc⟩

include fibD e SC SD cofC in
/-- 元の左右導来関手に対する、恒等関手から右左合成への自然なホモトピー候補。 -/
lemma quillenCfDerivedUnitHomotopy_nonempty :
    Nonempty (SSet.Homotopy (𝟙 (SimplicialNerve (CofibrantFibrantObjects C)))
      (quillenCfLeftDerived R adj fibD e SC SD ≫ quillenCfRightDerived R adj SC SD cofC)) := by
  obtain ⟨η, HL, HR, J, h0, h1, _⟩ :=
    quillenCfDerivedUnitPrism_exists R adj fibD e SC SD cofC
  refine ⟨{ h := (β_ _ (Δ[1] : SSet.{max u v})).hom ≫ η, h₀ := ?_, h₁ := ?_, rel := ?_ }⟩
  · change prismEndpoint 0 _ ≫ η = _
    exact h0
  · change prismEndpoint 1 _ ≫ η = _
    exact h1
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

end
end SerrePositivity.InfinityCategories.HomotopyLimits
