module

public import SerrePositivity.InfinityCategories.F1B.UnitCommaSquareComparisonPath
public import SerrePositivity.InfinityCategories.F1B.UnitCommaSquareRecovery
public import SerrePositivity.InfinityCategories.F1B.SquareTransportComparison
public import SerrePositivity.InfinityCategories.F1B.UnitCommaSquareHomotopyLift

/-!
概要：comma 正方形から取り出した経路による復元を、元の正方形と全境界固定で比較する。
方針：復元の三角形輸送を畳み込みで正方形へ移し、全体比較と同じ境界 path を確認する。
規約：正方形の族を同じパラメータ上で比較する。比較射の逆関係自体はまだ主張しない。
使われ方：B1 の写像空間比較の往復ホモトピーへの接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：元の comma 正方形と、その標的・全体比較の経路から復元した正方形は境界固定で結べる。
方針：元の全体 path と復元側の三角形の path の始点・三面を照合し、輸送の一意性を適用する。
規約：同じパラメータ上の復元の比較であり、普遍族の前合成との整合性は別途必要。
使われ方：順方向比較から戻る合成のホモトピーの構成。 -/
lemma unitCommaSquare_reconstruction_homotopy {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    ∃ H : SSet.Homotopy s.functorSquare
      (unitCommaSquareOfComparisonHomotopy η x w (unitCommaSquareTargetFamily η x w s)
        (unitCommaSquareComparisonHomotopy η x w s)).functorSquare,
      (squareBoundary.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        fst _ (Δ[1] : SSet.{u}) ≫ squareBoundary.ι ≫ s.functorSquare := by
  let f := unitCommaSquareTargetFamily η x w s
  let H := unitCommaSquareComparisonHomotopy η x w s
  let E := unitCompositionPathExtension η x (unitCommaFiberTargetVertex G x w) f H
  let T := unitIntervalCompositionTriangle_family η x (unitCommaFiberTargetVertex G x w) f
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
    exact (unitCompositionPathExtension_diagonal η x _ f H).trans
      (unitCommaSquareComparisonPath_right η x w s).symm
  obtain ⟨D, hD⟩ := (unitCommaSquareComparison η x w s).exists_homotopy_to_triangleTransport
    E.diagram E.start h₀ h₂ h₁
  have hr : (unitCommaSquareOfComparisonHomotopy η x w f H).functorSquare =
      squareUpperFold ≫ E.diagram ≫ equivalencePathEndpoint _ 1 := by
    rw [unitCommaSquareOfComparisonHomotopy_functorSquare, functorSquareOfCompositionTriangle_eq_fold]
    rfl
  let D' : SSet.Homotopy s.functorSquare
      (unitCommaSquareOfComparisonHomotopy η x w f H).functorSquare :=
    { h := D.h
      h₀ := D.h₀
      h₁ := D.h₁.trans hr.symm
      rel := D.rel }
  exact ⟨D', hD⟩

/-- 概要：元の comma 正方形の族と、同じパラメータ上で復元した族はホモトピック。
方針：全境界固定の正方形の比較を時間付き正方形へ転置し、写像空間の族へ戻す。
規約：普遍族から前合成した復元との同一視はまだ含めない。
使われ方：順方向から戻る合成のホモトピーの同じパラメータでの比較。 -/
lemma unitCommaSquare_reconstruction_family_homotopy {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    Nonempty (SSet.Homotopy s.family
      (unitCommaMappingFamilyOfComparisonHomotopy η x w (unitCommaSquareTargetFamily η x w s)
        (unitCommaSquareComparisonHomotopy η x w s))) := by
  obtain ⟨H, hH⟩ := unitCommaSquare_reconstruction_homotopy η x w s
  let t := unitCommaSquareOfComparisonHomotopy η x w (unitCommaSquareTargetFamily η x w s)
    (unitCommaSquareComparisonHomotopy η x w s)
  have ht : s.target = t.target := (unitCommaSquareTargetFamily_uncurry η x w s).symm
  exact ⟨(unitCommaSquareHomotopyLift s t H hH).familyHomotopy ht⟩

/-- 概要：comma の区間写像空間の族は、その正方形から同じパラメータ上で復元した族にホモトピック。
方針：正方形の族の復元比較と、族・正方形の厳密な全単射を使う。
規約：導来 fiber の普遍族で選んだ復元の前合成との比較は別途必要。
使われ方：B1 の戻る合成のホモトピーへの接続。 -/
lemma unitCommaMappingFamily_reconstruction_homotopy {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (f : A ⟶ intervalMappingSpace (unitCommaSectionVertex η x) w) :
    Nonempty (SSet.Homotopy f (unitCommaMappingFamilyOfComparisonHomotopy η x w
      (unitCommaSquareTargetFamily η x w (unitCommaFiberMappingSquare f))
      (unitCommaSquareComparisonHomotopy η x w (unitCommaFiberMappingSquare f)))) := by
  simpa only [unitCommaFiberMappingSquare_family] using
    unitCommaSquare_reconstruction_family_homotopy η x w (unitCommaFiberMappingSquare f)

end SerrePositivity.InfinityCategories
