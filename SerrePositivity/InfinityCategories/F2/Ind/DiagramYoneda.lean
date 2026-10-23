module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafSubcategory
public import SerrePositivity.InfinityCategories.F1.Universe.FunctorSpaceVertex
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition

/-!
概要：元の小さい coherent 図式全体への Ind Yoneda の作用。
方針：全内部 Hom の宇宙同型と元の Yoneda による後合成を使う。
規約：辺・高次単体を保持。使われ方：有限図式の単一 filtered 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の全 coherent 図式と変換を同じ Ind Yoneda で写す全射。 -/
def diagramYoneda (κ : Cardinal.{u}) (K C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj ((ihom K).obj C) ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj K)).obj (IndInfinity κ C) :=
  (uliftFunctorSpaceIso K C).hom ≫
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj K)).map (indYoneda κ C)

/-- 指定図式の像は元の全図式の持ち上げと Yoneda の合成そのもの。 -/
lemma diagramYoneda_vertex (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
    (a : K ⟶ C) :
    (diagramYoneda κ K C).app (Opposite.op ⦋0⦌) (ULift.up (functorVertex a)) =
      functorVertex ((SSet.uliftFunctor.{u + 1, u}).map a ≫ indYoneda κ C) := by
  change ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj K)).map (indYoneda κ C)).app _
    ((uliftFunctorSpaceIso K C).hom.app _ (ULift.up (functorVertex a))) = _
  rw [uliftFunctorSpaceIso_hom_vertex]
  rfl

/-- 元の全作用は形状の任意の制限と全次数で厳密に可換。 -/
lemma diagramYoneda_restrict (κ : Cardinal.{u}) {J K C : SSet.{u}}
    [Quasicategory C] (f : J ⟶ K) :
    (SSet.uliftFunctor.{u + 1, u}).map ((pre f).app C) ≫ diagramYoneda κ J C =
      diagramYoneda κ K C ≫ ((pre ((SSet.uliftFunctor.{u + 1, u}).map f)).app
        (IndInfinity κ C)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

/-- 元の図式版 Yoneda は全写像空間で充満忠実。形状の有限性も不要。 -/
lemma diagramYoneda_isFullyFaithful (κ : Cardinal.{u}) (K C : SSet.{u})
    [Quasicategory C] : IsFullyFaithful (diagramYoneda κ K C) :=
  (qCatEquivalenceOfIso (uliftFunctorSpaceIso K C)).isQCatEquivalence.isFullyFaithful.comp
    ((indYoneda_isFullyFaithful κ C).postcompose ((SSet.uliftFunctor.{u + 1, u}).obj K))

/-- 図式 Yoneda の全作用は、元の任意の頂点での評価と厳密に可換。 -/
lemma diagramYoneda_evaluate (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
    (k : K _⦋0⦌) :
    diagramYoneda κ K C ≫ evaluateFunctorAt (Y := IndInfinity κ C) (ULift.up k) =
      (SSet.uliftFunctor.{u + 1, u}).map (evaluateFunctorAt (Y := C) k) ≫ indYoneda κ C := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
