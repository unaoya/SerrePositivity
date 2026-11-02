module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomConjugation
/-!
概要：全 Hom 作用と三つの閉同型による共役を、指定した比較の貼り合わせで整理する。
方針：dg 関手と共役の交換、同型の連結、比較の全 Hom 自然性を順に適用する。
規約：任意の複体パラメータからの chain map を扱い、特定のラベル型に依存しない。
使われ方：表示模型の厳密合成則で、元の三重比較を全 Hom の等号へ送る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.KST.SConstruction
variable (A : Type u) [CommRing A] {C : Type v} {D : Type w}
  [DGCategory A C] [DGCategory A D] (G : DGFunctor A C D)
  {X X' Y Y' : ClosedCategory A C} {BX BY HX HY TX TY : ClosedCategory A D}
  {K : Complex A}

lemma dgFunctor_conjugation_pasting (a : K ⟶ (X ⟶[Complex A] Y))
    (eX : X ≅ X') (eY : Y ≅ Y')
    (bX : G.onClosed.obj X' ≅ BX) (bY : G.onClosed.obj Y' ≅ BY)
    (tX : BX ≅ TX) (tY : BY ≅ TY)
    (qX : G.onClosed.obj X ≅ HX) (qY : G.onClosed.obj Y ≅ HY)
    (cX : HX ≅ TX) (cY : HY ≅ TY) (h : K ⟶ (HX ⟶[Complex A] HY))
    (hX : G.onClosed.mapIso eX ≪≫ bX ≪≫ tX = qX ≪≫ cX)
    (hY : G.onClosed.mapIso eY ≪≫ bY ≪≫ tY = qY ≪≫ cY)
    (hn : a ≫ G.map (ForgetEnrichment.to (Complex A) X)
      (ForgetEnrichment.to (Complex A) Y) ≫
        enrichedClosedIsoConjugation (Complex A) qX qY = h) :
    a ≫ enrichedClosedIsoConjugation (Complex A) eX eY ≫
      G.map (ForgetEnrichment.to (Complex A) X') (ForgetEnrichment.to (Complex A) Y') ≫
      enrichedClosedIsoConjugation (Complex A) bX bY ≫
      enrichedClosedIsoConjugation (Complex A) tX tY =
    h ≫ enrichedClosedIsoConjugation (Complex A) cX cY := by
  have he := congrArg (fun k => a ≫ k ≫
    enrichedClosedIsoConjugation (Complex A) bX bY ≫
      enrichedClosedIsoConjugation (Complex A) tX tY)
    (dgFunctorHom_conjugation A G eX eY)
  simp only [Category.assoc] at he
  rw [he, enrichedClosedIsoConjugation_trans, enrichedClosedIsoConjugation_trans,
    hX, hY, ← enrichedClosedIsoConjugation_trans]
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ enrichedClosedIsoConjugation (Complex A) cX cY) hn

end SerrePositivity.DifferentialGraded
