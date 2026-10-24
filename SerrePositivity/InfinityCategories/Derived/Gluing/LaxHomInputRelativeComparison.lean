module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomInputHomotopies
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativePrismHomotopy

/-! # 入力固定変形と選択済み変形の相対比較

概要：同じ左右 Hom 入力を保つ実変形を、選択済み変形と二端固定で比較する。
方針：入力 fiber の実自明 Kan 射影に、既存の相対 prism 比較を適用する。
規約：比較は入力 fiber 内で行い、二次元族の基底像も時間方向に固定する。
使われ方：cube から得る実変形を指定三角形境界の選択済み二辺へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)


lemma dgGluingLaxHomFirstInputHomotopy_relative_comparison
    (H : SSet.Homotopy (dgGluingLaxHomFirstCompositionInputLift R C D M X Y)
      (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y))
    (hH : H.h ≫ dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      fst ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) (Δ[1] :
            SSet.{max (u + 1) v w}) ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y))) :
    ∃ T : SSet.Homotopy ((β_ (Δ[1] : SSet.{max (u + 1) v w}) ((SSet.uliftFunctor.{max (u + 1) v
      w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))).hom ≫ H.h)
        ((β_ (Δ[1] : SSet.{max (u + 1) v w}) ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))).hom ≫
          (dgGluingLaxHomFirstInputHomotopy R C D M X Y).h),
      (((boundary 1).ι ▷ ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))) ▷ (Δ[1] :
            SSet.{max (u + 1) v w})) ≫ T.h =
        fst ((boundary 1 : SSet.{max (u + 1) v w}) ⊗ ((SSet.uliftFunctor.{max (u + 1) v w, max
          u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))) Δ[1] ≫
          ((boundary 1).ι ▷ ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))) ≫ (β_ (Δ[1] :
            SSet.{max (u + 1) v w}) ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))).hom ≫
            (dgGluingLaxHomFirstInputHomotopy R C D M X Y).h ∧
      T.h ≫ dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
        fst ((Δ[1] : SSet.{max (u + 1) v w}) ⊗ ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))) Δ[1] ≫
          (β_ (Δ[1] : SSet.{max (u + 1) v w}) ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))).hom ≫
            (dgGluingLaxHomFirstInputHomotopy R C D M X Y).h ≫
              dgGluingDerivedFirstCompositionInputProjection R C D M X Y := by
  let := dgGluingDerivedFirstCompositionInputProjection_trivialKanFibration R C D M X Y
  apply dgGluingRelativePrismHomotopy_exists
    (dgGluingDerivedFirstCompositionInputProjection R C D M X Y)
  · have hi : prismEndpoint 0 ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ≫ (β_ (Δ[1] :
            SSet.{max (u + 1) v w}) ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))).hom = ι₀ := rfl
    simp only [← Category.assoc, hi, H.h₀, (dgGluingLaxHomFirstInputHomotopy R C D M X Y).h₀]
  · have hi : prismEndpoint 1 ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ≫ (β_ (Δ[1] :
            SSet.{max (u + 1) v w}) ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))).hom = ι₁ := rfl
    simp only [← Category.assoc, hi, H.h₁, (dgGluingLaxHomFirstInputHomotopy R C D M X Y).h₁]
  · rw [Category.assoc, hH, Category.assoc, dgGluingLaxHomFirstInputHomotopy_over]

lemma dgGluingLaxHomLastInputHomotopy_relative_comparison
    (H : SSet.Homotopy (dgGluingLaxHomLastCompositionInputLift R C D M X Y)
      (dgGluingHomDerivedLastCompositionInputLift R C D M X Y))
    (hH : H.h ≫ dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      fst ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) (Δ[1] :
            SSet.{max (u + 1) v w}) ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y))) :
    ∃ T : SSet.Homotopy ((β_ (Δ[1] : SSet.{max (u + 1) v w}) ((SSet.uliftFunctor.{max (u + 1) v
      w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))).hom ≫ H.h)
        ((β_ (Δ[1] : SSet.{max (u + 1) v w}) ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))).hom ≫
          (dgGluingLaxHomLastInputHomotopy R C D M X Y).h),
      (((boundary 1).ι ▷ ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))) ▷ (Δ[1] :
            SSet.{max (u + 1) v w})) ≫ T.h =
        fst ((boundary 1 : SSet.{max (u + 1) v w}) ⊗ ((SSet.uliftFunctor.{max (u + 1) v w, max
          u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))) Δ[1] ≫
          ((boundary 1).ι ▷ ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))) ≫ (β_ (Δ[1] :
            SSet.{max (u + 1) v w}) ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))).hom ≫
            (dgGluingLaxHomLastInputHomotopy R C D M X Y).h ∧
      T.h ≫ dgGluingDerivedLastCompositionInputProjection R C D M X Y =
        fst ((Δ[1] : SSet.{max (u + 1) v w}) ⊗ ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))) Δ[1] ≫
          (β_ (Δ[1] : SSet.{max (u + 1) v w}) ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))).hom ≫
            (dgGluingLaxHomLastInputHomotopy R C D M X Y).h ≫
              dgGluingDerivedLastCompositionInputProjection R C D M X Y := by
  let := dgGluingDerivedLastCompositionInputProjection_trivialKanFibration R C D M X Y
  apply dgGluingRelativePrismHomotopy_exists
    (dgGluingDerivedLastCompositionInputProjection R C D M X Y)
  · have hi : prismEndpoint 0 ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ≫ (β_ (Δ[1] :
            SSet.{max (u + 1) v w}) ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))).hom = ι₀ := rfl
    simp only [← Category.assoc, hi, H.h₀, (dgGluingLaxHomLastInputHomotopy R C D M X Y).h₀]
  · have hi : prismEndpoint 1 ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ≫ (β_ (Δ[1] :
            SSet.{max (u + 1) v w}) ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))).hom = ι₁ := rfl
    simp only [← Category.assoc, hi, H.h₁, (dgGluingLaxHomLastInputHomotopy R C D M X Y).h₁]
  · rw [Category.assoc, hH, Category.assoc, dgGluingLaxHomLastInputHomotopy_over]

end SerrePositivity.InfinityCategories
