module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyNaturalityData
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyFamilyWhiskering
public import SerrePositivity.KST.SConstruction.AssemblyCrossedFamilyBoundary
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CartesianFamilyEdgeTransport
public import SerrePositivity.KST.SConstruction.FactorizationDiagramPasting
public import SerrePositivity.KST.SConstruction.PointedNaturalityCompositionEdges
public import SerrePositivity.KST.SConstruction.AssemblyCompositionEdgeEvaluation
public import SerrePositivity.KST.SConstruction.KanAssemblyCompositionTriangle
public import SerrePositivity.KST.SConstruction.OneDirectionInverseCompositionTriangle

/-! # 随伴構造射の指定した自然性の合成三角形
概要：二本の入力と合成入力の指定した自然性の辺を同時に保つ実三角形を得る。
方針：三つの因子分解三角形・二つの因子合成三角形・交差正方形を貼る。
規約：パラメーター辺・因子辺・延長の選択を全て指定したまま使う。
使われ方：連結 K スペクトルの coherent な関手性の二入力の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra Spectra.PointedMapping
open scoped Simplicial

/-- 指定した自然性の三辺と全ての因子選択を保持する二入力の実合成三角形。 -/
lemma boundaryAssemblyCompositionTriangle_nonempty (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (vX : (boundaryKanAssemblyChoices r X) _⦋0⦌)
    (vY : (boundaryKanAssemblyChoices r Y) _⦋0⦌)
    (vZ : (boundaryKanAssemblyChoices r Z) _⦋0⦌)
    (dF : BoundaryAssemblyNaturalityData r f vX vY)
    (dG : BoundaryAssemblyNaturalityData r g vY vZ)
    (dFG : BoundaryAssemblyNaturalityData r (f ≫ g) vX vZ) :
    Nonempty (SSet.Edge.CompStruct
      (pointedNaturalityCompositionFirstEdge (boundaryKanRealizationFunctor r)
        (loopBoundaryKanFunctor (r + 1)) f g
        (boundaryKanAssemblyAdjointAt r X vX) (boundaryKanAssemblyAdjointAt r Y vY)
        (boundaryAssemblyChosenNaturalityEdge r f vX vY dF))
      (pointedNaturalityCompositionSecondEdge (boundaryKanRealizationFunctor r)
        (loopBoundaryKanFunctor (r + 1)) f g
        (boundaryKanAssemblyAdjointAt r Y vY) (boundaryKanAssemblyAdjointAt r Z vZ)
        (boundaryAssemblyChosenNaturalityEdge r g vY vZ dG))
      (boundaryAssemblyChosenNaturalityEdge r (f ≫ g) vX vZ dFG)) := by
  let post := (PointedObject.basedHomMap ((boundaryKanRealizationFunctor r).obj X)
    ((loopBoundaryKanFunctor (r + 1)).map g)).right
  let pre := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((boundaryKanRealizationFunctor r).map f)
    ((loopBoundaryKanFunctor (r + 1)).obj Z)).right
  let e₀₁ := pointedNaturalityCompositionFirstEdge (boundaryKanRealizationFunctor r)
    (loopBoundaryKanFunctor (r + 1)) f g
    (boundaryKanAssemblyAdjointAt r X vX) (boundaryKanAssemblyAdjointAt r Y vY)
    (boundaryAssemblyChosenNaturalityEdge r f vX vY dF)
  let e₁₂ := pointedNaturalityCompositionSecondEdge (boundaryKanRealizationFunctor r)
    (loopBoundaryKanFunctor (r + 1)) f g
    (boundaryKanAssemblyAdjointAt r Y vY) (boundaryKanAssemblyAdjointAt r Z vZ)
    (boundaryAssemblyChosenNaturalityEdge r g vY vZ dG)
  let e₀₂ := boundaryAssemblyChosenNaturalityEdge r (f ≫ g) vX vZ dFG
  change Nonempty (SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂)
  obtain ⟨tF⟩ := boundaryAssemblyNaturalityFactorizationTriangle_nonempty r f dF.evaluation
    vX vY dF.extension dF.inverse dF.parameter
  obtain ⟨tG⟩ := boundaryAssemblyNaturalityFactorizationTriangle_nonempty r g dG.evaluation
    vY vZ dG.extension dG.inverse dG.parameter
  obtain ⟨m₀₁, a₀₁, b₀₁, ha₀₁, hb₀₁, ⟨h₀₁⟩⟩ :=
    exists_mapped_factorization _ _ _ tF post e₀₁ rfl
  obtain ⟨m₁₂, a₁₂, b₁₂, ha₁₂, hb₁₂, ⟨h₁₂⟩⟩ :=
    exists_mapped_factorization _ _ _ tG pre e₁₂ rfl
  let a₀₂ := boundaryAssemblyExtensionEdgeAt r (f ≫ g) dFG.evaluation vX vZ dFG.extension
  let b₀₂ := boundaryAssemblyInverseEdgeAt r (f ≫ g) dFG.evaluation vX vZ dFG.inverse
  obtain ⟨h₀₂⟩ := boundaryAssemblyNaturalityFactorizationTriangle_nonempty r (f ≫ g)
    dFG.evaluation vX vZ dFG.extension dFG.inverse dFG.parameter
  obtain ⟨tE⟩ := kanAssemblyCompositionTriangle_nonempty r f g vX.2 vY.2 vZ.2
    dF.extension dG.extension dFG.extension
  obtain ⟨tI⟩ := oneDirectionInverseCompositionTriangle_nonempty r f g vX.1 vY.1 vZ.1
    dF.inverse dG.inverse dFG.inverse
  let lt := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeCompStruct (K := oneDirectionKanInverseChoices r X)
    (L := kanAssemblyMixedChoices r (f ≫ g))
    (SSet.Edge.CompStruct.idComp (SSet.Edge.id (X := oneDirectionKanInverseChoices r X) vX.1))
    tE).map (boundaryAssemblyExtensionFamily r (f ≫ g))
  let rt := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeCompStruct (K := oneDirectionInverseMixedChoices r (f ≫ g))
    (L := kanAssemblyAdjointChoices r Z) tI
    (SSet.Edge.CompStruct.idComp (SSet.Edge.id (X := kanAssemblyAdjointChoices r Z) vZ.2))).map
    (boundaryAssemblyInverseFamily r (f ≫ g))
  let cl := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeLowerTriangle (K := oneDirectionInverseMixedChoices r f)
    (L := kanAssemblyMixedChoices r g) dF.inverse dG.extension).map (assemblyCrossedFamily r f g)
  let cu := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeUpperTriangle (K := oneDirectionInverseMixedChoices r f)
    (L := kanAssemblyMixedChoices r g) dF.inverse dG.extension).map (assemblyCrossedFamily r f g)
  have hl₀₁ := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianLeftFamilyEdge_square (kanAssemblyMixedPost r f g)
    (boundaryAssemblyExtensionFamily r f) (boundaryAssemblyExtensionFamily r (f ≫ g)) post
    (boundaryAssemblyExtensionFamily_post r f g) vX.1 dF.extension).trans
    ((congrArg (post.app (Opposite.op ⦋1⦌))
      (boundaryAssemblyExtensionEdgeAt_evaluation r f dF.evaluation vX vY dF.extension).symm).trans
        ha₀₁.symm)
  have hl₀₂ := (boundaryAssemblyExtensionEdgeAt_evaluation r (f ≫ g)
    dFG.evaluation vX vZ dFG.extension).symm
  have hr₁₂ := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianRightFamilyEdge_square (oneDirectionInverseMixedPre r f g)
    (boundaryAssemblyInverseFamily r g) (boundaryAssemblyInverseFamily r (f ≫ g)) pre
    (boundaryAssemblyInverseFamily_pre r f g) vZ.2 dG.inverse).trans
    ((congrArg (pre.app (Opposite.op ⦋1⦌))
      (boundaryAssemblyInverseEdgeAt_evaluation r g dG.evaluation vY vZ dG.inverse).symm).trans
        hb₁₂.symm)
  have hr₀₂ := (boundaryAssemblyInverseEdgeAt_evaluation r (f ≫ g)
    dFG.evaluation vX vZ dFG.inverse).symm
  have hp₀₁ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianRightFamilyEdge_parameter (kanAssemblyMixedFromSource r g)
    (assemblyCrossedFamily r f g) vY.2 dF.inverse
  have hq₀₁ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mappedEdge_family_congr _ _ (assemblyCrossedFamily_extension_source r f g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionInverseMixedChoices r f)
      (L := kanAssemblyAdjointChoices r Y) dF.inverse (SSet.Edge.id vY.2))
  have hv₀₁ := boundaryAssemblyInverseEdgeAt_evaluation r f dF.evaluation vX vY dF.inverse
  simp only [SSet.Edge.map_edge, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at hp₀₁ hq₀₁ hv₀₁ hb₀₁
  have hc₀₁ := hp₀₁.trans (hq₀₁.trans
    ((congrArg (post.app (Opposite.op ⦋1⦌)) hv₀₁.symm).trans hb₀₁.symm))
  have hp₁₃ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianLeftFamilyEdge_parameter (oneDirectionInverseMixedFromTarget r f)
    (assemblyCrossedFamily r f g) vY.1 dG.extension
  have hq₁₃ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mappedEdge_family_congr _ _ (assemblyCrossedFamily_inverse_target r f g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionKanInverseChoices r Y)
      (L := kanAssemblyMixedChoices r g) (SSet.Edge.id vY.1) dG.extension)
  have hv₁₃ := boundaryAssemblyExtensionEdgeAt_evaluation r g dG.evaluation vY vZ dG.extension
  simp only [SSet.Edge.map_edge, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at hp₁₃ hq₁₃ hv₁₃ ha₁₂
  have hc₁₃ := hp₁₃.trans (hq₁₃.trans
    ((congrArg (pre.app (Opposite.op ⦋1⦌)) hv₁₃.symm).trans ha₁₂.symm))
  have hp₀₂ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianLeftFamilyEdge_parameter (oneDirectionInverseMixedFromSource r f)
    (assemblyCrossedFamily r f g) vX.1 dG.extension
  have hq₀₂ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mappedEdge_family_congr _ _ (assemblyCrossedFamily_inverse_source r f g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionKanInverseChoices r X)
      (L := kanAssemblyMixedChoices r g) (SSet.Edge.id vX.1) dG.extension)
  have hm₀₂ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianLeftFamilyEdge_moving (kanAssemblyMixedPre r f g)
    (boundaryAssemblyExtensionFamily r (f ≫ g)) vX.1 dG.extension
  simp only [SSet.Edge.map_edge, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at hp₀₂ hq₀₂ hm₀₂
  have hc₀₂ := hp₀₂.trans (hq₀₂.trans hm₀₂.symm)
  have hp₂₃ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianRightFamilyEdge_parameter (kanAssemblyMixedFromTarget r g)
    (assemblyCrossedFamily r f g) vZ.2 dF.inverse
  have hq₂₃ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mappedEdge_family_congr _ _ (assemblyCrossedFamily_extension_target r f g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionInverseMixedChoices r f)
      (L := kanAssemblyAdjointChoices r Z) dF.inverse (SSet.Edge.id vZ.2))
  have hm₂₃ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianRightFamilyEdge_moving (oneDirectionInverseMixedPost r f g)
    (boundaryAssemblyInverseFamily r (f ≫ g)) vZ.2 dF.inverse
  simp only [SSet.Edge.map_edge, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at hp₂₃ hq₂₃ hm₂₃
  have hc₂₃ := hp₂₃.trans (hq₂₃.trans hm₂₃.symm)
  let l₀₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionKanInverseChoices r X)
    (L := kanAssemblyMixedChoices r (f ≫ g)) (SSet.Edge.id vX.1)
    (kanAssemblyCompositionFirstEdge r f g vX.2 vY.2 dF.extension)).map
      (boundaryAssemblyExtensionFamily r (f ≫ g))
  let l₁₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionKanInverseChoices r X)
    (L := kanAssemblyMixedChoices r (f ≫ g)) (SSet.Edge.id vX.1)
    (kanAssemblyCompositionSecondEdge r f g vY.2 vZ.2 dG.extension)).map
      (boundaryAssemblyExtensionFamily r (f ≫ g))
  let l₀₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionKanInverseChoices r X)
    (L := kanAssemblyMixedChoices r (f ≫ g)) (SSet.Edge.id vX.1) dFG.extension).map
      (boundaryAssemblyExtensionFamily r (f ≫ g))
  let r₀₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionInverseMixedChoices r (f ≫ g))
    (L := kanAssemblyAdjointChoices r Z)
    (oneDirectionInverseCompositionFirstEdge r f g vX.1 vY.1 dF.inverse)
    (SSet.Edge.id vZ.2)).map (boundaryAssemblyInverseFamily r (f ≫ g))
  let r₁₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionInverseMixedChoices r (f ≫ g))
    (L := kanAssemblyAdjointChoices r Z)
    (oneDirectionInverseCompositionSecondEdge r f g vY.1 vZ.1 dG.inverse)
    (SSet.Edge.id vZ.2)).map (boundaryAssemblyInverseFamily r (f ≫ g))
  let r₀₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionInverseMixedChoices r (f ≫ g))
    (L := kanAssemblyAdjointChoices r Z) dFG.inverse (SSet.Edge.id vZ.2)).map
      (boundaryAssemblyInverseFamily r (f ≫ g))
  let c₀₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionInverseMixedChoices r f)
    (L := kanAssemblyMixedChoices r g) dF.inverse
    (SSet.Edge.id ((kanAssemblyMixedFromSource r g).app (Opposite.op ⦋0⦌) vY.2))).map
      (assemblyCrossedFamily r f g)
  let c₁₃ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionInverseMixedChoices r f)
    (L := kanAssemblyMixedChoices r g)
    (SSet.Edge.id ((oneDirectionInverseMixedFromTarget r f).app (Opposite.op ⦋0⦌) vY.1))
    dG.extension).map (assemblyCrossedFamily r f g)
  let c₀₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionInverseMixedChoices r f)
    (L := kanAssemblyMixedChoices r g)
    (SSet.Edge.id ((oneDirectionInverseMixedFromSource r f).app (Opposite.op ⦋0⦌) vX.1))
    dG.extension).map (assemblyCrossedFamily r f g)
  let c₂₃ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionInverseMixedChoices r f)
    (L := kanAssemblyMixedChoices r g) dF.inverse
    (SSet.Edge.id ((kanAssemblyMixedFromTarget r g).app (Opposite.op ⦋0⦌) vZ.2))).map
      (assemblyCrossedFamily r f g)
  let c₀₃ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (K := oneDirectionInverseMixedChoices r f)
    (L := kanAssemblyMixedChoices r g) dF.inverse dG.extension).map (assemblyCrossedFamily r f g)
  refine nonemptyCompStruct_paste_factorization_diagram
    (K := (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
      ((loopBoundaryKanFunctor (r + 1)).obj Z)).right)
    a₀₁ b₀₁ e₀₁ a₁₂ b₁₂ e₁₂ a₀₂ b₀₂ e₀₂ ?_ ?_ ?_
    l₀₁ l₁₂ l₀₂ r₀₁ r₁₂ r₀₂ c₀₁ c₁₃ c₀₂ c₂₃ c₀₃ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact h₀₁
  · exact h₁₂
  · exact h₀₂
  · exact lt
  · exact rt
  · exact cl
  · exact cu
  · exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianLeftFamilyEdge_congr (boundaryAssemblyExtensionFamily r (f ≫ g)) vX.1
      (kanAssemblyCompositionFirstEdge r f g vX.2 vY.2 dF.extension)
      (dF.extension.map (kanAssemblyMixedPost r f g))
      (kanAssemblyCompositionFirstEdge_edge r f g vX.2 vY.2 dF.extension)).trans hl₀₁
  · exact hl₀₂
  · exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianRightFamilyEdge_congr (boundaryAssemblyInverseFamily r (f ≫ g)) vZ.2
      (oneDirectionInverseCompositionSecondEdge r f g vY.1 vZ.1 dG.inverse)
      (dG.inverse.map (oneDirectionInverseMixedPre r f g))
      (oneDirectionInverseCompositionSecondEdge_edge r f g vY.1 vZ.1 dG.inverse)).trans hr₁₂
  · exact hr₀₂
  · exact hc₀₁
  · exact hc₁₃
  · exact hc₀₂.trans (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianLeftFamilyEdge_congr
      (boundaryAssemblyExtensionFamily r (f ≫ g)) vX.1
      (kanAssemblyCompositionSecondEdge r f g vY.2 vZ.2 dG.extension)
      (dG.extension.map (kanAssemblyMixedPre r f g))
      (kanAssemblyCompositionSecondEdge_edge r f g vY.2 vZ.2 dG.extension)).symm
  · exact hc₂₃.trans (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cartesianRightFamilyEdge_congr
      (boundaryAssemblyInverseFamily r (f ≫ g)) vZ.2
      (oneDirectionInverseCompositionFirstEdge r f g vX.1 vY.1 dF.inverse)
      (dF.inverse.map (oneDirectionInverseMixedPost r f g))
      (oneDirectionInverseCompositionFirstEdge_edge r f g vX.1 vY.1 dF.inverse)).symm

end SerrePositivity.KST.SConstruction
