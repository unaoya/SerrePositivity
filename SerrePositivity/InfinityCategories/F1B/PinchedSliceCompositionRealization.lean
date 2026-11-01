module
public import SerrePositivity.InfinityCategories.F1B.PinchedSliceTransport
public import SerrePositivity.InfinityCategories.F1B.PinchedFamilyHomotopy
public import SerrePositivity.InfinityCategories.F1B.HomotopyCompositionOver

/-!
概要：全パラメータの合成方程式から、同じ全底と合成三角形を持つ実 slice 比較を構成する。
方針：終端固定の輸送の始点を pinched fiber の実ホモトピーで補正し、指定底で貼る。
規約：底の二単体全体も保持する。使われ方：任意標的の屋根評価の全選択空間比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open CartesianMonoidalCategory MonoidalClosed
/-- 実輸送・始点の fiber 比較・合成三角形と、その指定された全底。 -/
structure PinchedSliceCompositionRealization {K X : SSet.{u}} {x y z : X _⦋0⦌}
    (f : K ⟶ pinchedHom x y) (g : K ⟶ pinchedHom y z) (c : K ⟶ pinchedHom x z) where
  transport : PinchedSliceTransportFamily f g
  coefficientHomotopy : SSet.Homotopy c transport.coefficient
  homotopy : SSet.Homotopy (c ≫ pinchedFamilySlice X x z) (g ≫ pinchedFamilySlice X y z)
  comparisonTriangle : FunctorCompositionTriangle
    (functorHomotopyPostcomp coefficientHomotopy (pinchedFamilySlice X x z))
    transport.homotopy homotopy
  triangle_over : comparisonTriangle.diagram ≫
    (ihom K).map (sliceOverProjection (SSet.yonedaEquiv.symm z)) =
      functorIdentityCompositionDiagram (functorHomotopyPostcomp transport.homotopy
        (sliceOverProjection (SSet.yonedaEquiv.symm z)))
  over : homotopy.h ≫ sliceOverProjection _ =
    (intervalFamilyHomotopy (f ≫ pinchedHomToIntervalMappingSpace x y)).h
/-- 関手圏内の合成方程式は、同じ底と合成三角形を持つ実 slice 比較として実現できる。 -/
lemma pinchedSliceCompositionRealization_nonempty {K X : SSet.{u}} [Quasicategory X]
    {x y z : X _⦋0⦌} (f : K ⟶ pinchedHom x y) (g : K ⟶ pinchedHom y z)
    (c : K ⟶ pinchedHom x z)
    (hc : intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace x y) ≫
      intervalFamilyHom (g ≫ pinchedHomToIntervalMappingSpace y z) =
        intervalFamilyHom (c ≫ pinchedHomToIntervalMappingSpace x z)) :
    Nonempty (PinchedSliceCompositionRealization f g c) := by
  obtain ⟨R⟩ := pinchedSliceTransportFamily_nonempty f g
  have hR := pinchedSliceHomotopyFamily_comp f g R.coefficient R.homotopy R.over
  obtain ⟨J⟩ := pinchedFamilyHom_eq_iff_homotopy.mp (hc.symm.trans hR)
  let p := sliceOverProjection (SSet.yonedaEquiv.symm z)
  let l := functorHomotopyPostcomp J (pinchedFamilySlice X x z)
  have hl : l.h ≫ p = fst K (Δ[1] : SSet.{u}) ≫
      (R.coefficient ≫ pinchedFamilySlice X x z) ≫ p := by
    change (J.h ≫ pinchedFamilySlice X x z) ≫ p =
      fst K (Δ[1] : SSet.{u}) ≫ (R.coefficient ≫ pinchedFamilySlice X x z) ≫ p
    dsimp only [p]
    simp only [Category.assoc, pinchedFamilySlice_projection, SSet.comp_const]
  obtain ⟨d, T, hT, hd⟩ := homotopyCompositionOver_fixedLeft_exists p l R.homotopy hl
  exact ⟨⟨R, J, d, T, hT, hd.trans R.over⟩⟩
/-- 指定合成方程式から、指定始点と終点・全底を持つ実 slice ホモトピーを回収する。 -/
lemma pinchedSliceHomotopyFamily_exists_of_comp {K X : SSet.{u}} [Quasicategory X]
    {x y z : X _⦋0⦌} (f : K ⟶ pinchedHom x y) (g : K ⟶ pinchedHom y z)
    (c : K ⟶ pinchedHom x z)
    (hc : intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace x y) ≫
      intervalFamilyHom (g ≫ pinchedHomToIntervalMappingSpace y z) =
        intervalFamilyHom (c ≫ pinchedHomToIntervalMappingSpace x z)) :
    ∃ H : SSet.Homotopy (c ≫ pinchedFamilySlice X x z) (g ≫ pinchedFamilySlice X y z),
      H.h ≫ sliceOverProjection _ =
        (intervalFamilyHomotopy (f ≫ pinchedHomToIntervalMappingSpace x y)).h := by
  obtain ⟨R⟩ := pinchedSliceCompositionRealization_nonempty f g c hc
  exact ⟨R.homotopy, R.over⟩
end SerrePositivity.InfinityCategories
