module

public import SerrePositivity.InfinityCategories.F1.RightFibrationYoneda
public import SerrePositivity.InfinityCategories.Core.VertexFiberNervePullback
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeFunctorPostcomposition
public import SerrePositivity.InfinityCategories.Core.PinchedSlice

/-!
概要：right fibration 版 Yoneda 評価の自然性と、二つの表現可能対象間の写像空間比較。
方針：正規化した評価を fiber の包含後に照合し、標準 pinched 模型との同型を合成する。
規約：写像空間の比較は元の恒等点評価そのもの。Yoneda ∞ 関手の構成とは区別する。
使われ方：F1-2 の Yoneda の写像空間上の比較と、前層への後合成の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 正規化した Yoneda 評価は、全空間の包含後には元の恒等点評価そのもの。 -/
lemma rightFibrationSlicePointEvaluate_ι {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    rightFibrationSlicePointEvaluate p b ≫ vertexFiberι p b =
      vertexFiberι
        ((ihom (sliceOver (SSet.yonedaEquiv.symm b))).map p)
        (functorVertex (sliceOverProjection (SSet.yonedaEquiv.symm b))) ≫
          evaluateFunctorAt (sliceIdentityCone b) := by
  rw [rightFibrationSlicePointEvaluate, Category.assoc,
    vertexFiberTransport_ι p (sliceIdentityCone_projection b), relativeFunctorEvaluate_ι]

/-- Yoneda の全空間評価は、底を保つ実際の射による後合成と厳密に可換。 -/
lemma rightFibrationSlicePointEvaluate_post {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    relativeFunctorPost p q f hf (sliceOverProjection (SSet.yonedaEquiv.symm b)) ≫
        rightFibrationSlicePointEvaluate q b =
      rightFibrationSlicePointEvaluate p b ≫ vertexFiberMap p q f hf b := by
  have ht (x y : B _⦋0⦌) (h : x = y) :
      vertexFiberMap p q f hf x ≫ eqToHom (congrArg (vertexFiber q) h) =
        eqToHom (congrArg (vertexFiber p) h) ≫ vertexFiberMap p q f hf y := by
    subst y
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  dsimp only [rightFibrationSlicePointEvaluate]
  rw [← Category.assoc, relativeFunctorPost_evaluate, Category.assoc,
    ht _ _ (sliceIdentityCone_projection b), ← Category.assoc]

/-- 表現可能な二つの right fibrations 間の相対射を、元の標準写像空間へ送る。 -/
def rightFibrationRepresentableMappingComparison {B : SSet.{u}} (a b : B _⦋0⦌) :
    relativeFunctorSpace (sliceOverProjection (SSet.yonedaEquiv.symm b))
      (sliceOverProjection (SSet.yonedaEquiv.symm a)) ⟶ pinchedHom a b :=
  rightFibrationSlicePointEvaluate (sliceOverProjection (SSet.yonedaEquiv.symm b)) a ≫
    (pinchedHomSliceFiberIso a b).inv

/-- 表現可能対象間の実際の写像比較は、全境界の持ち上げを持つ。 -/
lemma rightFibrationRepresentableMappingComparison_trivialKanFibration
    {B : SSet.{u}} [Quasicategory B] (a b : B _⦋0⦌) :
    TrivialKanFibration (rightFibrationRepresentableMappingComparison a b) :=
  ⟨trivialKanFibrations.comp_mem _ _
    (rightFibrationSlicePointEvaluate_trivialKanFibration
      (sliceOverProjection (SSet.yonedaEquiv.symm b)) a).mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 表現可能 right fibrations 間の全相対写像空間は、元の ∞ 圏の写像空間と同値。 -/
lemma rightFibrationRepresentableMappingComparison_isQCatEquivalence
    {B : SSet.{u}} [Quasicategory B] (a b : B _⦋0⦌) :
    IsQCatEquivalence (rightFibrationRepresentableMappingComparison a b) := by
  have := rightFibrationRepresentableMappingComparison_trivialKanFibration a b
  exact isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories
