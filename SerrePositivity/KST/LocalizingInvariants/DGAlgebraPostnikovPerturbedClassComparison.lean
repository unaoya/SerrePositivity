module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPerturbedClass
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeBoundary

/-!
概要：実 Postnikov class は、元の cone の線形 class と二座標を保って一致する。
方針：底射影は元の全射準同型分解、係数射影は標準 cone 境界の負符号で比較する。
規約：元の係数同型と符号を保持。使われ方：隣接拡大の実 pullback との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

lemma postnikovPerturbedClass_hom_eq : (postnikovPerturbedClass R B n hn).hom =
    (postnikovPerturbedExtensionComplexIso R B n hn).hom ≫
      postnikovExtensionConeLinearClass R B n hn := by
  apply biprod.hom_ext
  · change (postnikovPerturbedClass R B n hn).hom ≫
      (SquareZero.projection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)).hom = _
    calc
      _ = (postnikovPerturbedProjection R B n hn).hom :=
        congrArg Mon.Hom.hom (postnikovPerturbedClass_projection R B n hn)
      _ = (postnikovPerturbedExtensionComplexIso R B n hn).hom ≫
          postnikovExtensionConeProjection R B n := postnikovPerturbedProjection_hom_eq R B n hn
      _ = _ := by
        exact (congrArg (fun t => (postnikovPerturbedExtensionComplexIso R B n hn).hom ≫ t)
          (postnikovExtensionConeLinearClass_projection R B n hn)).symm.trans
            (Category.assoc _ _ _).symm
  · let σ : (postnikovDerivationTarget R B n hn).X ⟶
        (postnikovShiftedLayerBimodule R B n hn 1).X := biprod.snd
    change (postnikovPerturbedClass R B n hn).hom ≫ σ =
      ((postnikovPerturbedExtensionComplexIso R B n hn).hom ≫
        postnikovExtensionConeLinearClass R B n hn) ≫ σ
    have hs : postnikovExtensionConeLinearClass R B n hn ≫ σ =
        (mappingCone.triangle (postnikovLayerInclusion R B n)).mor₃ :=
      cochainConeToSplit_snd _ _ _
    rw [Category.assoc, hs]
    apply HomologicalComplex.hom_ext
    intro p
    have hm := congrArg (fun t => t.f p) (biprod.map_snd
      (postnikovTransition R B (n + 1) n (by omega)).hom
      (-(𝟙 ((postnikovLayerBimodule R B n).X⟦(1 : ℤ)⟧))))
    simp only [HomologicalComplex.comp_f, HomologicalComplex.neg_f_apply, HomologicalComplex.id_f,
      Preadditive.comp_neg, Category.comp_id] at hm
    have hl : ((postnikovPerturbedClass R B n hn).hom ≫ σ).f p =
        -SquareZeroCone.coefficientF (postnikov R B (n + 1)) (postnikovLayerBimodule R B n)
          (postnikovLayerInclusion R B n) p := by
      change (postnikovPerturbedClass R B n hn).hom.f p ≫ σ.f p = _
      rw [postnikovPerturbedClass_f]
      exact hm
    exact hl.trans (SquareZeroCone.complexIso_boundary_f (postnikov R B (n + 1))
      (postnikovLayerBimodule R B n) (postnikovLayerInclusion R B n) p).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
