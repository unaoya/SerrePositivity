module

public import SerrePositivity.InfinityCategories.F1B.UnitCommaReconstructionComparison
public import SerrePositivity.InfinityCategories.F1B.UnitCompositionTransportParameters

/-!
概要：普遍パラメータ上で選んだ復元を前合成した族と元の comma の族を比較する。
方針：制限した輸送が同じ始点・境界 path を持つことを使い、全境界固定の比較を族へ移す。
規約：輸送を選び直す操作と元の輸送の前合成を同一視しない。
使われ方：B1 の実際の戻る比較射の合成のホモトピー。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：元の comma 正方形の族は、別パラメータ上の復元を前合成した族にホモトピック。
方針：標的族と raw なホモトピーの一致から元の輸送を制限し、正方形全体の輸送と比較する。
規約：同じ端点だけでは足りず、入力ホモトピーの射そのものの一致を仮定する。
使われ方：普遍族で定義した戻る射の合成を元の族へ結ぶ。 -/
lemma unitCommaSquare_reconstruction_precomp_homotopy {A B X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A)
    (i : A ⟶ B)
    (f : B ⟶ intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (unitCommaFiberTargetVertex G x w))
    (H : SSet.Homotopy (f ≫ unitIntervalMap η x (unitCommaFiberTargetVertex G x w))
      (unitCommaArrowFamily G x w B))
    (hf : i ≫ f = unitCommaSquareTargetFamily η x w s)
    (hH : (unitCommaSquareComparisonHomotopy η x w s).h = (i ▷ (Δ[1] : SSet.{u})) ≫ H.h) :
    Nonempty (SSet.Homotopy s.family (i ≫ unitCommaMappingFamilyOfComparisonHomotopy η x w f H)) := by
  let f₀ := unitCommaSquareTargetFamily η x w s
  let H₀ := unitCommaSquareComparisonHomotopy η x w s
  let E := unitCompositionPathExtension_precomp η x (unitCommaFiberTargetVertex G x w)
    i f₀ f H₀ H hf hH
  let T := unitIntervalCompositionTriangle_family η x (unitCommaFiberTargetVertex G x w) f₀
  have h₀ : stdSimplex.δ (0 : Fin 3) ≫ E.diagram =
      stdSimplex.δ (0 : Fin 3) ≫ T.diagram ≫ equivalencePathRefl _ := by
    rw [← boundary.ι_ι (0 : Fin 3), Category.assoc, E.restriction]
    exact triangleBoundaryPath_face_zero _ _ _ _
  have h₂ : stdSimplex.δ (2 : Fin 3) ≫ E.diagram =
      stdSimplex.δ (2 : Fin 3) ≫ T.diagram ≫ equivalencePathRefl _ := by
    rw [← boundary.ι_ι (2 : Fin 3), Category.assoc, E.restriction]
    exact triangleBoundaryPath_face_two _ _ _ _
  have h₁ : stdSimplex.δ (1 : Fin 3) ≫ E.diagram =
      prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ (unitCommaSquareComparison η x w s).path := by
    rw [← boundary.ι_ι (1 : Fin 3), Category.assoc, E.restriction,
      unitCompositionBoundaryPath_diagonal]
    exact (unitCommaSquareComparisonPath_right η x w s).symm
  obtain ⟨D, hD⟩ := (unitCommaSquareComparison η x w s).exists_homotopy_to_triangleTransport
    E.diagram E.start h₀ h₂ h₁
  let t := (unitCommaSquareOfComparisonHomotopy η x w f H).precomp i
  have ht : s.target = t.target := by
    rw [UnitCommaFiberSquare.precomp_target]
    change s.target = ((Δ[1] : SSet.{u}) ◁ i) ≫ intervalMappingUncurry f
    rw [← intervalMappingUncurry_precomp, hf, unitCommaSquareTargetFamily_uncurry]
  have hr : t.functorSquare = squareUpperFold ≫ E.diagram ≫ equivalencePathEndpoint _ 1 := by
    rw [UnitCommaFiberSquare.precomp_functorSquare,
      unitCommaSquareOfComparisonHomotopy_functorSquare, functorSquareOfCompositionTriangle_eq_fold]
    change (squareUpperFold ≫
      ((unitCompositionPathExtension η x (unitCommaFiberTargetVertex G x w) f H).diagram ≫
        equivalencePathEndpoint _ 1)) ≫ (pre i).app X =
      squareUpperFold ≫
        ((unitCompositionPathExtension η x (unitCommaFiberTargetVertex G x w) f H).diagram ≫
          equivalencePathMap ((pre i).app X)) ≫ equivalencePathEndpoint _ 1
    simp only [Category.assoc, equivalencePathMap_endpoint]
  let D' : SSet.Homotopy s.functorSquare t.functorSquare :=
    { h := D.h
      h₀ := D.h₀
      h₁ := D.h₁.trans hr.symm
      rel := D.rel }
  have h := (unitCommaSquareHomotopyLift s t D' hD).familyHomotopy ht
  have htf : t.family = i ≫ unitCommaMappingFamilyOfComparisonHomotopy η x w f H :=
    UnitCommaFiberSquare.precomp_family _ _
  exact ⟨by simpa only [htf] using h⟩

end SerrePositivity.InfinityCategories
