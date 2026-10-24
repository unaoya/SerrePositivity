module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.RelativePathEndpointComparison
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorPointHomotopy
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorDiagramTransport

/-!
概要：同じ始点と同じ制限 path を持つ図式の輸送の終点を相対的に比較する。
方針：関手単体集合の相対 path 写像へ移し、基底上の比較を元の図式へ戻す。
規約：終点のホモトピーは指定部分図式を全時間で保持する。
使われ方：B1 の元の comma 正方形と復元側の境界輸送の一意性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：同じ始点・制限 path を持つ図式の輸送の終点は相対ホモトピック。
方針：相対 path 写像の持ち上げを比較し、零単体表示の比較を元の図式へ戻す。
規約：部分図式への射は単射、値域は quasicategory。
使われ方：指定境界 path の二つの拡張の比較。 -/
lemma exists_functorDiagramPath_endpointHomotopy {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (L M : B ⟶ equivalencePath X)
    (hpath : i ≫ L = i ≫ M)
    (hstart : L ≫ equivalencePathEndpoint X 0 = M ≫ equivalencePathEndpoint X 0) :
    ∃ D : SSet.Homotopy (L ≫ equivalencePathEndpoint X 1) (M ≫ equivalencePathEndpoint X 1),
      (i ▷ (Δ[1] : SSet.{u})) ≫ D.h =
        fst A (Δ[1] : SSet.{u}) ≫ i ≫ M ≫ equivalencePathEndpoint X 1 := by
  let p := (pre i).app X
  have : TrivialKanFibration (relativeEquivalencePathMap p) :=
    trivialKanFibration_relativeEquivalencePathMap_pre i X
  let a := functorDiagramPathEquiv B X L
  let b := functorDiagramPathEquiv B X M
  have hp : a ≫ equivalencePathMap p = b ≫ equivalencePathMap p := by
    change functorDiagramPathEquiv B X L ≫ equivalencePathMap ((pre i).app X) =
      functorDiagramPathEquiv B X M ≫ equivalencePathMap ((pre i).app X)
    rw [functorDiagramPathEquiv_precomp, functorDiagramPathEquiv_precomp, hpath]
  have hs : a ≫ equivalencePathEndpoint _ 0 = b ≫ equivalencePathEndpoint _ 0 := by
    change functorDiagramPathEquiv B X L ≫ equivalencePathEndpoint _ 0 =
      functorDiagramPathEquiv B X M ≫ equivalencePathEndpoint _ 0
    rw [functorDiagramPathEquiv_endpoint, functorDiagramPathEquiv_endpoint, hstart]
  obtain ⟨H, hH⟩ := exists_relativePathEndpointHomotopy p a b hp hs
  let H' : SSet.Homotopy
      (functorDiagramPointEquiv B X (L ≫ equivalencePathEndpoint X 1))
      (functorDiagramPointEquiv B X (M ≫ equivalencePathEndpoint X 1)) :=
    { h := H.h
      h₀ := H.h₀.trans (functorDiagramPathEquiv_endpoint L 1)
      h₁ := H.h₁.trans (functorDiagramPathEquiv_endpoint M 1)
      rel := H.rel }
  have hH' : H'.h ≫ (pre i).app X = fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
      functorDiagramPointEquiv A X (i ≫ (M ≫ equivalencePathEndpoint X 1)) := by
    change H.h ≫ p = _
    rw [hH]
    change fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
      (functorDiagramPathEquiv B X M ≫ equivalencePathEndpoint _ 1) ≫ (pre i).app X = _
    rw [functorDiagramPathEquiv_endpoint, functorDiagramPointEquiv_precomp]
  exact exists_relativeFunctorPointHomotopy i H' hH'

/-- 概要：同じ指定境界 path と始点の二つの拡張の終点を境界固定で比較する。
方針：拡張の制限・始点の仕様を輸送の相対一意性へ渡す。
規約：境界の終点だけでなく指定 path 全体を共有する。
使われ方：B1 の構成した全体比較と復元側の境界輸送の比較。 -/
lemma FunctorDiagramPathExtension.exists_endpointHomotopy {A B X : SSet.{u}} [Quasicategory X]
    {i : A ⟶ B} [Mono i] {Q : A ⟶ equivalencePath X} {F : B ⟶ X}
    (L M : FunctorDiagramPathExtension i Q F) :
    ∃ D : SSet.Homotopy (L.diagram ≫ equivalencePathEndpoint X 1)
      (M.diagram ≫ equivalencePathEndpoint X 1),
      (i ▷ (Δ[1] : SSet.{u})) ≫ D.h = fst A (Δ[1] : SSet.{u}) ≫ Q ≫
        equivalencePathEndpoint X 1 := by
  obtain ⟨D, hD⟩ := exists_functorDiagramPath_endpointHomotopy i L.diagram M.diagram
    (L.restriction.trans M.restriction.symm) (L.start.trans M.start.symm)
  refine ⟨D, ?_⟩
  simpa only [Category.assoc, reassoc_of% M.restriction] using hD

end SerrePositivity.InfinityCategories
