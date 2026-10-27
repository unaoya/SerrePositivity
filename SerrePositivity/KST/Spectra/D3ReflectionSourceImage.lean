module

public import SerrePositivity.KST.Spectra.D3LoopReflectionImage

/-!
概要：指定全図式の転置比較の像を、始点反転の同じ全関手作用まで回収する。
方針：充満忠実な逆像の各角と、反転を定めた端点正規化の指定値を追う。
規約：元の全図式像が loop 図式である場合だけを使う。新しい極限保存仮定は置かない。
使われ方：BF の段構造と、次段の通常 loop 像との反転の整合。
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
lemma d3LoopReflectionImage_source_eq :
    (H ≫ loopDiagramEvaluation X 0 0) ≫ f = G ≫ loopDiagramEvaluation Y 0 0 := by
  let evY := evaluateFunctorAt (X := ((Δ[1] : SSet.{u}) ⊗ Δ[1])) (Y := Y)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  have heval : (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map f ≫ evY =
      evaluateFunctorAt (Y := X)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫ f := rfl
  have h := congrArg (fun k ↦ k ≫ evY) hG
  simpa only [loopDiagramEvaluation, Category.assoc, heval] using h

omit [HasZeroVertex Y] in
/-- 指定像の各角でも、元の指定全図式比較への同じ後合成を回収する。 -/
lemma d3LoopImageTransposeIso_corner (i j : Fin 2) :
    HEq ((d3LoopImageTransposeIso sX hsX H G f hG).postcomp
      (loopDiagramEvaluation Y i j))
      ((((d3LoopDiagramTransposeIso sX hsX).precomp H).postcomp
        (loopDiagramEvaluation X i j)).postcomp f) := by
  let ιY := (fullSubcomplexOnVertices
    ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj Y) IsLoopDiagramVertex).ι
  let p := (fullSubcomplexOnVertices
    ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) IsLoopDiagramVertex).ι ≫
      (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map f
  let evY := evaluateFunctorAt (X := ((Δ[1] : SSet.{u}) ⊗ Δ[1])) (Y := Y)
    (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)
  let e := ((d3LoopDiagramTransposeIso sX hsX).precomp H).postcomp p
  have heval : p ≫ evY = loopDiagramEvaluation X i j ≫ f := rfl
  have h0 := d3LoopImageTransposeIso_projection sX hsX H G f hG
  have h1 := F2.functorIso_postcomp_heq_of_heq e
    ((d3LoopImageTransposeIso sX hsX H G f hG).postcomp ιY)
    (show (H ≫ 𝟙 _) ≫ p = G ≫ ιY from by
      simpa only [p, ιY, Category.comp_id, Category.assoc] using hG)
    (d3LoopImageTranspose_target H G f hG) h0 evY
  have h2 := F2.functorIso_postcomp_postcomp
    (d3LoopImageTransposeIso sX hsX H G f hG) ιY evY
  have h3 := F2.functorIso_postcomp_postcomp
    ((d3LoopDiagramTransposeIso sX hsX).precomp H) p evY
  have h4 := F2.functorIso_postcomp_heq_of_map_eq
    ((d3LoopDiagramTransposeIso sX hsX).precomp H) heval
  have h5 := F2.functorIso_postcomp_postcomp
    ((d3LoopDiagramTransposeIso sX hsX).precomp H) (loopDiagramEvaluation X i j) f
  exact (heq_of_eq h2.symm).trans (h1.trans
    ((heq_of_eq h3).trans (h4.symm.trans (heq_of_eq h5.symm))))

private lemma d3LoopImageTransposeIso_source_reflection :
    HEq ((d3LoopImageTransposeIso sX hsX H G f hG).postcomp (loopDiagramEvaluation Y 0 0))
      ((d3LoopDiagramReflection sY hsY).precomp G) := by
  rw [d3LoopImageTransposeIso_eq sX hsX sY hsY]
  have h0 := functorIsoOfEq_postcomp_heq
    ((d3LoopDiagramTransposeIso sY hsY).precomp G) (Category.comp_id G) rfl
    (loopDiagramEvaluation Y 0 0)
  have h1 := F2.functorIso_precomp_postcomp (d3LoopDiagramTransposeIso sY hsY) G
    (loopDiagramEvaluation Y 0 0)
  have h2 := functorIsoOfEq_precomp_heq
    ((d3LoopDiagramTransposeIso sY hsY).postcomp (loopDiagramEvaluation Y 0 0))
    (Category.id_comp _) (d3LoopDiagramTranspose_corner Y 0 0) G
  exact h0.trans ((heq_of_eq h1).trans h2.symm)

include hG in
/-- 始点反転の同じ指定値は、既証の実全図式の像に対して後合成と交換する。 -/
lemma d3LoopReflectionImage_source_heq :
    HEq (((d3LoopDiagramReflection sX hsX).precomp H).postcomp f)
      ((d3LoopDiagramReflection sY hsY).precomp G) := by
  have h0 := functorIsoOfEq_precomp_heq
    ((d3LoopDiagramTransposeIso sX hsX).postcomp (loopDiagramEvaluation X 0 0))
    (Category.id_comp _) (d3LoopDiagramTranspose_corner X 0 0) H
  have h1 := F2.functorIso_postcomp_heq_of_heq
    (((d3LoopDiagramTransposeIso sX hsX).postcomp (loopDiagramEvaluation X 0 0)).precomp H)
    ((d3LoopDiagramReflection sX hsX).precomp H)
    (by simp only [Category.id_comp])
    (by simp only [d3LoopDiagramTranspose_corner]) h0 f
  have h2 := congrArg (fun k ↦ FunctorIso.postcomp k f)
    (F2.functorIso_precomp_postcomp (d3LoopDiagramTransposeIso sX hsX) H
      (loopDiagramEvaluation X 0 0))
  exact h1.trans ((heq_of_eq h2.symm).trans
    ((d3LoopImageTransposeIso_corner sX hsX H G f hG 0 0).symm.trans
      (d3LoopImageTransposeIso_source_reflection sX hsX sY hsY H G f hG)))

/-- 端点表示を同じ値へ正規化すると、始点反転の像は像側の同じ反転に厳密一致する。 -/
lemma d3LoopReflectionImage_source :
    F2.functorIsoOfEq (((d3LoopDiagramReflection sX hsX).precomp H).postcomp f)
      (d3LoopReflectionImage_source_eq H G f hG) (d3LoopReflectionImage_source_eq H G f hG) =
    (d3LoopDiagramReflection sY hsY).precomp G :=
  eq_of_heq ((F2.functorIsoOfEq_heq _ _ _).trans
    (d3LoopReflectionImage_source_heq sX hsX sY hsY H G f hG))

end
end SerrePositivity.KST.Spectra
