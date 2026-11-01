module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomWhiskering
public import SerrePositivity.DifferentialGraded.Functor.DGClosedIsoConjugationLaws

/-! # dg Hom 作用と実閉零同型の共役
概要：dg 関手の Hom 作用が、実閉零同型による全次数の共役と可換である。
方針：元の閉零射の前後合成との交換を順に適用する。
規約：同型の像は同じ閉零関手による像。使われ方：ラベル付き Perf の合成法則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {C : Type v} {D : Type w}
  [DGCategory A C] [DGCategory A D] (F : DGFunctor A C D)

/-- 全 Hom の共役は、元の dg 関手の Hom 作用を通して同じ同型の像の共役になる。 -/
lemma dgFunctorHom_conjugation {X X' Y Y' : ClosedCategory A C}
    (e : X ≅ X') (f : Y ≅ Y') :
    enrichedClosedIsoConjugation (Complex A) e f ≫
        F.map (ForgetEnrichment.to (Complex A) X') (ForgetEnrichment.to (Complex A) Y') =
      F.map (ForgetEnrichment.to (Complex A) X) (ForgetEnrichment.to (Complex A) Y) ≫
        enrichedClosedIsoConjugation (Complex A) (F.onClosed.mapIso e) (F.onClosed.mapIso f) := by
  unfold enrichedClosedIsoConjugation
  rw [Category.assoc, dgFunctorHom_postcompose, ← Category.assoc,
    dgFunctorHom_precompose, Category.assoc]
  rfl

end SerrePositivity.KST.SConstruction
