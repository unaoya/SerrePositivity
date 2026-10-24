module
public import SerrePositivity.KST.NonConnective.DGKappaSplitModuleCells
public import SerrePositivity.KST.SConstruction.CofiberCompletion
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorTranspose
public import SerrePositivity.InfinityCategories.Stable.CurryVertexEvaluation

/-!
概要：元の全 native 分裂四角形を、D-12 の明示入力の下で cofiber 図式の実族にする。
方針：同じ二変数の作用を転置し、各ラベルで検証した cofiber 条件で全部分圏へ持ち上げる。
規約：D-12 の入力を省かず、各対象で独立に図式を選び直さない。
使われ方：同じ cone の連結 K の加法性と swindle の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective

private lemma transpose_vertex {A B P : SSet.{u}} (F : P ⟶ (ihom A).obj B)
    (x : A _⦋0⦌) :
    (F1B.functorTranspose F).app (Opposite.op ⦋0⦌) x =
      functorVertex (F ≫ evaluateFunctorAt x) := by
  change (curry ((β_ P A).hom ≫ uncurry F)).app (Opposite.op ⦋0⦌) x = _
  rw [curry_vertex_evaluation]
  have he := curry_evaluation_vertex (uncurry F) x
  rw [curry_uncurry] at he
  rw [he]
  rfl

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (Z : DGKappaZeroInput R D I)

/-- 同じ全 native 四角形を転置した、元の Perf 上の全四角形図式の族。 -/
def dgKappaSplitPerfDiagramFamily :=
  F1B.functorTranspose (dgKappaSplitPerfFamilySquare R D I Z)

/-- 転置した元の図式族の各ラベルは、同じ指定二胞体を持つ点ごとの四角形。 -/
theorem dgKappaSplitPerfDiagramFamily_vertex
    (X : PresentedPerfectDGObject R (DGKappaCone R D I)) :
    (dgKappaSplitPerfDiagramFamily R D I Z).app (Opposite.op ⦋0⦌) (Simplex.vertex X) =
      functorVertex (dgKappaSplitPerfPointwiseSquare R D I X Z) :=
  transpose_vertex _ _

/-- D-12 の明示入力の下で、同じ全作用は cofiber 図式の全部分圏に値を取る。 -/
def dgKappaSplitCofiberFamily
    (H : ∀ X : PresentedPerfectDGObject R (DGKappaCone R D I),
      DGKappaSplitCofiberInput R D I X) :
    dgNerve R (PresentedPerfectDGObject R (DGKappaCone R D I)) ⟶
      cofiberDiagrams (dgNerve R (PresentedPerfectDGObject R (DGKappaCone R D I))) :=
  fullSubcomplexLift IsCofiberDiagramVertex (dgKappaSplitPerfDiagramFamily R D I Z) (by
    intro x
    obtain ⟨X, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
    change IsCofiberDiagramVertex
      ((dgKappaSplitPerfDiagramFamily R D I Z).app (Opposite.op ⦋0⦌) (Simplex.vertex X))
    rw [dgKappaSplitPerfDiagramFamily_vertex]
    dsimp only [IsCofiberDiagramVertex, IsPushoutDiagramVertex]
    rw [squareDiagram_functorVertex]
    exact ⟨(dgKappaSplitPerfPointwiseZeroTriangle R D I X Z).zero_corner,
      dgKappaSplitPerfPointwiseSquare_isPushout_of_input R D I X (H X) Z⟩)

/-- cofiber 図式の包含後も、同じ元の全単体的四角形族に厳密一致する。 -/
theorem dgKappaSplitCofiberFamily_ι
    (H : ∀ X : PresentedPerfectDGObject R (DGKappaCone R D I),
      DGKappaSplitCofiberInput R D I X) :
    dgKappaSplitCofiberFamily R D I Z H ≫
        (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
      dgKappaSplitPerfDiagramFamily R D I Z :=
  fullSubcomplexLift_ι _ _ _

end SerrePositivity.KST.NonConnective
