module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPerturbedMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPerturbedClass

/-!
概要：元の dg 代数射に対する Postnikov の負符号の実 class の厳密な自然性。
方針：底と shift 層の実射で標的射を作り、元の二座標で可換性を証明する。
規約：選択した cell lift を入力しない。使われ方：その後の相対経路比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

def postnikovDerivationTargetMap : postnikovDerivationTarget R B n hn ⟶
    postnikovDerivationTarget R C n hn :=
  SquareZero.mapOver (postnikovMap R f n) (postnikovShiftedLayerBimodule R B n hn 1)
    (postnikovShiftedLayerBimodule R C n hn 1) (postnikovShiftedLayerMap R B n hn 1 f)

lemma postnikovDerivationTargetMap_hom : (postnikovDerivationTargetMap R f n hn).hom =
    biprod.map (postnikovMap R f n).hom ((postnikovLayerMap R f n)⟦(1 : ℤ)⟧') := by
  change biprod.map (postnikovMap R f n).hom
    (postnikovShiftedLayerMap R B n hn 1 f).hom = _
  rw [postnikovShiftedLayerMap_hom]
  rfl

lemma postnikovDerivationTargetMap_coefficient : (postnikovDerivationTargetMap R f n hn).hom ≫
    (biprod.snd : (postnikovDerivationTarget R C n hn).X ⟶
      (postnikovShiftedLayerBimodule R C n hn 1).X) =
      (biprod.snd : (postnikovDerivationTarget R B n hn).X ⟶
        (postnikovShiftedLayerBimodule R B n hn 1).X) ≫
          (postnikovShiftedLayerMap R B n hn 1 f).hom :=
  biprod.map_snd _ _

lemma postnikovDerivationTargetMap_projection : postnikovDerivationTargetMap R f n hn ≫
    SquareZero.projection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1) =
      SquareZero.projection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1) ≫
        postnikovMap R f n := SquareZero.mapOver_projection _ _ _ _

lemma postnikovDerivationTargetMap_zeroSection :
    SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1) ≫
      postnikovDerivationTargetMap R f n hn = postnikovMap R f n ≫
        SquareZero.zeroSection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1) :=
  SquareZero.zeroSection_mapOver _ _ _ _

lemma postnikovPerturbedClass_naturality : postnikovPerturbedMap R f n hn ≫
    postnikovPerturbedClass R C n hn =
      postnikovPerturbedClass R B n hn ≫ postnikovDerivationTargetMap R f n hn := by
  apply Mon.Hom.ext
  apply HomologicalComplex.hom_ext
  intro p
  change (postnikovPerturbedMap R f n hn).hom.f p ≫
    (postnikovPerturbedClass R C n hn).hom.f p =
      (postnikovPerturbedClass R B n hn).hom.f p ≫ (postnikovDerivationTargetMap R f n hn).hom.f p
  rw [postnikovPerturbedMap_f, postnikovPerturbedClass_f, postnikovPerturbedClass_f,
    postnikovDerivationTargetMap_hom]
  have ht : (postnikovMap R f (n + 1)).hom ≫
      (postnikovTransition R C (n + 1) n (by omega)).hom =
      (postnikovTransition R B (n + 1) n (by omega)).hom ≫ (postnikovMap R f n).hom :=
    congrArg Mon.Hom.hom (postnikovTransition_naturality R B f (n + 1) n (by omega))
  have he : biprod.map (postnikovMap R f (n + 1)).hom ((postnikovLayerMap R f n)⟦(1 : ℤ)⟧') ≫
      biprod.map (postnikovTransition R C (n + 1) n (by omega)).hom
        (-(𝟙 ((postnikovLayer R C n)⟦(1 : ℤ)⟧))) =
      biprod.map (postnikovTransition R B (n + 1) n (by omega)).hom
        (-(𝟙 ((postnikovLayer R B n)⟦(1 : ℤ)⟧))) ≫
          biprod.map (postnikovMap R f n).hom ((postnikovLayerMap R f n)⟦(1 : ℤ)⟧') := by
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst]
      rw [← Category.assoc, biprod.map_fst, Category.assoc, ht, biprod.map_fst_assoc]
    · simp [Category.assoc]
  exact congrArg (fun t => t.f p) he

lemma postnikovPerturbedProjection_naturality : postnikovPerturbedMap R f n hn ≫
    postnikovPerturbedProjection R C n hn =
      postnikovPerturbedProjection R B n hn ≫ postnikovMap R f n := by
  rw [← postnikovPerturbedClass_projection, ← Category.assoc,
    postnikovPerturbedClass_naturality, Category.assoc,
    postnikovDerivationTargetMap_projection, ← Category.assoc,
    postnikovPerturbedClass_projection]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
