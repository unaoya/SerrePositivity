module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DoldKanClosedPostcomposition
public import SerrePositivity.EInfinity.ComplexLimits.ComplexPinchedPostcomposition

/-!
概要：複体の Γ Hom 関手を、同じ閉射圏の豊穣 Hom 関手と全自然同型で結ぶ。
方針：指定 Hom 同型を成分にし、閉後合成と元の複体射の一致で自然性を示す。
規約：元の複体と全複体射を保つ。対象ごとの同型で終えない。
使われ方：HA 1.2.4、G10 の指定 BK 錐から native 錐への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- 元の Hom 複体の smart 切断と Γ による、全複体射上の Hom 空間関手。 -/
def complexDoldKanHomFunctor (P : Complex A) : Complex A ⥤ SSet.{u} :=
  homFunctor P ⋙ (ComplexShape.embeddingUpIntLE 0).truncLE'Functor (ModuleCat.{u} A) ⋙
    (Abelian.DoldKan.Γ : ChainComplex (ModuleCat.{u} A) ℕ ⥤ SimplicialObject (ModuleCat.{u} A)) ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat.{u} A) (Type u)).obj
        (forget (ModuleCat.{u} A))

/-- 指定 Γ 同型を、豊穣 Hom と元の複体の Hom の全関手同型にする。 -/
def complexDoldKanHomIso (P : Complex A) :
    SerrePositivity.EInfinity.ComplexLimits.complexToClosed A ⋙
      (SimplicialCategory.sHomFunctor (ClosedCategory A (Complex A))).obj
        (op (ForgetEnrichment.of (Complex A) P)) ≅ complexDoldKanHomFunctor A P :=
  NatIso.ofComponents (fun Q => doldKanSimplicialHomIso (R := A)
    (ForgetEnrichment.of (Complex A) P) (ForgetEnrichment.of (Complex A) Q)) (by
      intro Q T f
      have h := doldKanSimplicialHomIso_postcomposition A (Complex A) P Q T
        ((SerrePositivity.EInfinity.ComplexLimits.complexToClosed A).map f)
      rw [SerrePositivity.EInfinity.ComplexLimits.complexToClosed_postcomposition] at h
      exact h)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
