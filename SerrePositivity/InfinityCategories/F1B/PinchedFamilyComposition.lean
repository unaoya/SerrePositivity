module
public import SerrePositivity.InfinityCategories.F1B.SlicePrismFamilyComposition

/-!
概要：実 pinched Hom の三族と slice prism から h Fun の合成関係を得る。
方針：区間表示と実 slice の境界を同じ四角形へ接続する。
規約：任意の標的・全パラメータを扱う。使われ方：実屋根の四三角形族の評価。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
/-- 任意の実 pinched Hom の target slice への標準包含。 -/
noncomputable def pinchedFamilySlice (X : SSet.{u}) (x y : X _⦋0⦌) :
    pinchedHom x y ⟶ sliceOver (SSet.yonedaEquiv.symm y) :=
  (pinchedHomSliceFiberIso x y).hom ≫ vertexFiberι _ x
/-- 同じ三境界と全射影を持つ実 prism は、三つの族の合成を h Fun で与える。 -/
lemma pinchedPrismFamily_comp {K X : SSet.{u}} {x y z : X _⦋0⦌}
    (f : K ⟶ pinchedHom x y) (g : K ⟶ pinchedHom y z) (c : K ⟶ pinchedHom x z)
    (P : (Δ[1] : SSet.{u}) ⊗ K ⟶ sliceOver (SSet.yonedaEquiv.symm z))
    (h₀ : prismEndpoint 0 K ≫ P = c ≫ pinchedFamilySlice X x z)
    (h₁ : prismEndpoint 1 K ≫ P = g ≫ pinchedFamilySlice X y z)
    (hp : P ≫ sliceOverProjection _ =
      intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace x y)) :
    intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace x y) ≫
      intervalFamilyHom (g ≫ pinchedHomToIntervalMappingSpace y z) =
        intervalFamilyHom (c ≫ pinchedHomToIntervalMappingSpace x z) := by
  apply slicePrismFamily_comp z
    (intervalFamilyHomotopy (f ≫ pinchedHomToIntervalMappingSpace x y))
    (intervalFamilyHomotopy (c ≫ pinchedHomToIntervalMappingSpace x z))
    (intervalFamilyHomotopy (g ≫ pinchedHomToIntervalMappingSpace y z)) P
  · rw [h₀]
    change _ = (β_ K (Δ[1] : SSet.{u})).hom ≫
      intervalMappingUncurry (c ≫ pinchedHomToIntervalMappingSpace x z)
    rw [pinchedHomToIntervalMappingSpace_uncurry]
    rfl
  · rw [h₁]
    change _ = (β_ K (Δ[1] : SSet.{u})).hom ≫
      intervalMappingUncurry (g ≫ pinchedHomToIntervalMappingSpace y z)
    rw [pinchedHomToIntervalMappingSpace_uncurry]
    rfl
  · exact congrArg (fun k => (β_ K (Δ[1] : SSet.{u})).hom ≫ k) hp
/-- 同じ全射影を持つ実 slice ホモトピーも、三つの族の合成を与える。 -/
lemma pinchedSliceHomotopyFamily_comp {K X : SSet.{u}} {x y z : X _⦋0⦌}
    (f : K ⟶ pinchedHom x y) (g : K ⟶ pinchedHom y z) (c : K ⟶ pinchedHom x z)
    (H : SSet.Homotopy (c ≫ pinchedFamilySlice X x z) (g ≫ pinchedFamilySlice X y z))
    (hp : H.h ≫ sliceOverProjection _ =
      (intervalFamilyHomotopy (f ≫ pinchedHomToIntervalMappingSpace x y)).h) :
    intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace x y) ≫
      intervalFamilyHom (g ≫ pinchedHomToIntervalMappingSpace y z) =
        intervalFamilyHom (c ≫ pinchedHomToIntervalMappingSpace x z) := by
  apply pinchedPrismFamily_comp f g c ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h)
  · change SSet.ι₀ ≫ H.h = _
    exact H.h₀
  · change SSet.ι₁ ≫ H.h = _
    exact H.h₁
  · rw [Category.assoc, hp]
    dsimp only [intervalFamilyHomotopy]
    simp only [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
end SerrePositivity.InfinityCategories
