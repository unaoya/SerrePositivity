module

public import SerrePositivity.KST.Spectra.D3NativeLoopReflection
public import SerrePositivity.KST.Spectra.D3StageLoopDiagramFamily

/-!
概要：実 loop 全図式の転置比較は、同じ全図式を後合成した像の転置比較に一致する。
方針：元の指定比較を全四角形で後合成し、全部分圏と終点評価の充満忠実性で回収する。
規約：選択族に既証の loop 像だけを使う。任意の関手の極限保存を仮定しない。
使われ方：nativeLoop の全体反転と各段反転の、同じ全図式における照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

private lemma d3EqIso_normalized_post {A B C : SSet.{u}} {f g f' g' : A ⟶ B}
    (e : FunctorIso f g) (hf : f = f') (hg : g = g') (p : B ⟶ C)
    (h : F2.IsFunctorEqIso (e.postcomp p)) :
    F2.IsFunctorEqIso ((F2.functorIsoOfEq e hf hg).postcomp p) :=
  h.of_heq (congrArg (fun a ↦ a ≫ p) hf) (congrArg (fun a ↦ a ≫ p) hg)
    (functorIsoOfEq_postcomp_heq e hf hg p)

section
variable {A X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  [HasZeroVertex X] [HasZeroVertex Y]
  (sX : X ⟶ loopDiagrams X) (hsX : sX ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
  (sY : Y ⟶ loopDiagrams Y) (hsY : sY ≫ loopDiagramEvaluation Y 1 1 = 𝟙 Y)
  (H : A ⟶ loopDiagrams X) (G : A ⟶ loopDiagrams Y) (f : X ⟶ Y)
  (hG : H ≫ (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫
    (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map f =
      G ≫ (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι)

omit [Quasicategory X] [Quasicategory Y] [HasZeroVertex X] [HasZeroVertex Y] in
include hG in
lemma d3LoopImageTranspose_target :
    (H ≫ d3LoopDiagramTranspose X) ≫
        ((fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫
          (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map f) =
      (G ≫ d3LoopDiagramTranspose Y) ≫
        (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι := by
  calc
    _ = H ≫ (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫
        (pre (β_ (Δ[1] : SSet.{u}) Δ[1]).hom).app X ≫
          (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map f := by
      simpa only [Category.assoc] using congrArg (fun k ↦ H ≫ k ≫
        (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map f) (d3LoopDiagramTranspose_ι X)
    _ = (H ≫ (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫
        (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map f) ≫
          (pre (β_ (Δ[1] : SSet.{u}) Δ[1]).hom).app Y := by
      rw [← (pre (β_ (Δ[1] : SSet.{u}) Δ[1]).hom).naturality f]
      simp only [Category.assoc]
    _ = _ := by
      rw [hG]
      simpa only [Category.assoc] using
        (congrArg (fun k ↦ G ≫ k) (d3LoopDiagramTranspose_ι Y)).symm

/-- 元の指定転置比較を、同じ全四角形の像に施した実 loop 全図式比較。 -/
def d3LoopImageTransposeIso : FunctorIso G (G ≫ d3LoopDiagramTranspose Y) :=
  (isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj Y) IsLoopDiagramVertex).preimageFunctorIso
      (F2.functorIsoOfEq
        (((d3LoopDiagramTransposeIso sX hsX).precomp H).postcomp
          ((fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫
            (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map f))
        (by simpa only [Category.comp_id, Category.assoc] using hG)
        (d3LoopImageTranspose_target H G f hG))

omit [HasZeroVertex Y] in
lemma d3LoopImageTransposeIso_target_isEq :
    F2.IsFunctorEqIso ((d3LoopImageTransposeIso sX hsX H G f hG).postcomp
      (loopDiagramEvaluation Y 1 1)) := by
  let ιY := (fullSubcomplexOnVertices
    ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj Y) IsLoopDiagramVertex).ι
  let p := (fullSubcomplexOnVertices
    ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) IsLoopDiagramVertex).ι ≫
      (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map f
  let ev := evaluateFunctorAt (X := ((Δ[1] : SSet.{u}) ⊗ Δ[1])) (Y := Y)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  let e := ((d3LoopDiagramTransposeIso sX hsX).precomp H).postcomp p
  have hraw : F2.IsFunctorEqIso (e.postcomp ev) := by
    have heval : p ≫ ev = loopDiagramEvaluation X 1 1 ≫ f := rfl
    have hb := ((d3LoopDiagramTransposeIso_target_isEq sX hsX).precomp H).postcomp f
    have hh : HEq (e.postcomp ev)
        (((d3LoopDiagramTransposeIso sX hsX).postcomp
          (loopDiagramEvaluation X 1 1)).precomp H |>.postcomp f) := by
      have h0 := F2.functorIso_postcomp_postcomp
        ((d3LoopDiagramTransposeIso sX hsX).precomp H) p ev
      have h1 := F2.functorIso_postcomp_heq_of_map_eq
        ((d3LoopDiagramTransposeIso sX hsX).precomp H) heval
      have h2 := F2.functorIso_postcomp_postcomp
        ((d3LoopDiagramTransposeIso sX hsX).precomp H) (loopDiagramEvaluation X 1 1) f
      have h3 := congrArg (fun k ↦ FunctorIso.postcomp k f)
        (F2.functorIso_precomp_postcomp (d3LoopDiagramTransposeIso sX hsX) H
          (loopDiagramEvaluation X 1 1))
      exact (heq_of_eq h0).trans (h1.symm.trans
        ((heq_of_eq h2.symm).trans (heq_of_eq h3)))
    exact hb.of_heq
      (by simp only [Category.assoc, heval])
      (by simp only [Category.assoc, heval]) hh
  have hn := d3EqIso_normalized_post e
    (show (H ≫ 𝟙 _) ≫ p = G ≫ ιY from by
      simpa only [p, ιY, Category.comp_id, Category.assoc] using hG)
    (d3LoopImageTranspose_target H G f hG) ev hraw
  let hiY := isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj Y) IsLoopDiagramVertex
  have hi := hiY.preimageFunctorIso_postcomp (F2.functorIsoOfEq e
        (show (H ≫ 𝟙 _) ≫ p = G ≫ ιY from by
          simpa only [p, ιY, Category.comp_id, Category.assoc] using hG)
        (d3LoopImageTranspose_target H G f hG))
  have hh := congrArg (fun k ↦ FunctorIso.postcomp k ev) hi
  rw [F2.functorIso_postcomp_postcomp] at hh
  change F2.IsFunctorEqIso
    ((d3LoopImageTransposeIso sX hsX H G f hG).postcomp (ιY ≫ ev))
  rw [show (d3LoopImageTransposeIso sX hsX H G f hG).postcomp (ιY ≫ ev) = _ from hh]
  exact hn

omit [HasZeroVertex Y] in
/-- 回収した実 loop 全図式比較の周囲の四角形は、元の指定比較の同じ後合成。 -/
lemma d3LoopImageTransposeIso_projection :
    HEq ((d3LoopImageTransposeIso sX hsX H G f hG).postcomp
      (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι)
      (((d3LoopDiagramTransposeIso sX hsX).precomp H).postcomp
        ((fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫
          (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map f)) :=
by
  let hiY := isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj Y) IsLoopDiagramVertex
  exact hiY.preimageNormalizedFunctorIso_postcomp_heq G (G ≫ d3LoopDiagramTranspose Y)
        (((d3LoopDiagramTransposeIso sX hsX).precomp H).postcomp
          ((fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫
            (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map f))
        (by simpa only [Category.comp_id, Category.assoc] using hG)
        (d3LoopImageTranspose_target H G f hG)

/-- 同じ全図式の像の比較は、像側で定まる指定転置比較そのもの。 -/
lemma d3LoopImageTransposeIso_eq :
    d3LoopImageTransposeIso sX hsX H G f hG =
      F2.functorIsoOfEq ((d3LoopDiagramTransposeIso sY hsY).precomp G)
        (Category.comp_id G) rfl := by
  let := loopDiagramEvaluation_target_trivialKanFibration_of_section Y sY hsY
  let hf := isFullyFaithful_of_trivialKanFibration (loopDiagramEvaluation Y 1 1)
  apply hf.postcomp_functorIso_injective
  have h0 := d3LoopImageTransposeIso_target_isEq sX hsX H G f hG
  have h1 : F2.IsFunctorEqIso (((d3LoopDiagramTransposeIso sY hsY).precomp G).postcomp
      (loopDiagramEvaluation Y 1 1)) := by
    rw [F2.functorIso_precomp_postcomp]
    exact (d3LoopDiagramTransposeIso_target_isEq sY hsY).precomp G
  exact d3FunctorEqIso_unique h0 (d3EqIso_normalized_post _ _ _ _ h1)

end

namespace OmegaSpectrum.AdjointLoopRelativeBF
open SerrePositivity.KST.SConstruction
local instance d3ReflectionImageSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の実全図式の指定転置比較の段像は、同じ実段 loop 図式の指定転置比較を回収する。 -/
lemma commonChosenStageReflectionImageIso_eq (n : ℕ) :
    d3LoopImageTransposeIso nativeLoopTargetEquivalence.{u}.inv
      nativeLoopTargetEquivalence_inv_target commonChosenLoopDiagramFamily
      (commonChosenStageLoopDiagramFamily n) (coherentNerveMap (d3StageKanEnriched n))
      (by rw [commonChosenStageLoopDiagramFamily_ι]; rfl) =
    F2.functorIsoOfEq
      ((d3LoopDiagramTransposeIso d3PointedKanLoopSection
        d3PointedKanLoopSection_target).precomp (commonChosenStageLoopDiagramFamily n))
      (Category.comp_id _) rfl :=
  d3LoopImageTransposeIso_eq nativeLoopTargetEquivalence.inv
    nativeLoopTargetEquivalence_inv_target d3PointedKanLoopSection
    d3PointedKanLoopSection_target _ _ _ _

end OmegaSpectrum.AdjointLoopRelativeBF
end SerrePositivity.KST.Spectra
