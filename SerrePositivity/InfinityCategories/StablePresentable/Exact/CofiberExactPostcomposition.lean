module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.Pointed
public import SerrePositivity.InfinityCategories.Core.Pullback
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.Core.SuspensionDiagrams
public import SerrePositivity.InfinityCategories.Core.TerminalVertices
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams
public import SerrePositivity.InfinityCategories.Stable.ExactFunctor
public import SerrePositivity.InfinityCategories.StablePresentable.Exact.ExactArrowMap

/-!
概要：完全関手は普遍 cofiber 四角形の全族を、指定した底辺と cofiber 頂点ごと写す。
方針：零角と押し出しの保存で全部分複体に持ち上げ、評価との交換を保持する。
規約：全単体上の関手を構成する。使われ方：cofiber 関手の coherent な自然比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
variable {X Y : SSet.{u}} [Quasicategory X] [IsStable X]
  [Quasicategory Y] [IsStable Y] (F : X ⟶ Y) [IsExactFunctor F]

omit [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y] [IsExactFunctor F] in
lemma squareDiagram_postcomp
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌) :
    squareDiagram (((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map F).app (Opposite.op ⦋0⦌) v) =
      squareDiagram v ≫ F := by
  obtain ⟨R, rfl⟩ := (functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) X).surjective v
  change squareDiagram (functorVertex (R ≫ F)) = squareDiagram (functorVertex R) ≫ F
  exact ((functorVertexEquiv _ _).symm_apply_apply (R ≫ F)).trans
    (congrArg (· ≫ F) ((functorVertexEquiv _ _).symm_apply_apply R).symm)

def postcomp : space X ⟶ space Y :=
  fullSubcomplexLift Predicate (inclusion X ≫ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map F) (by
    intro v
    have hv := fullSubcomplexOnVertices_vertex v
    change IsZeroVertex (squareVertex (squareDiagram
      (((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map F).app (Opposite.op ⦋0⦌) v.val)) 0 1) ∧ _
    rw [squareDiagram_postcomp]
    exact ⟨IsExactFunctor.preservesZero (F := F) _ hv.1,
      IsExactFunctor.preservesPushoutSquare F _ hv.2⟩)

lemma postcomp_inclusion : postcomp F ≫ inclusion Y =
    inclusion X ≫ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map F :=
  fullSubcomplexLift_ι _ _ _

lemma postcomp_bottom : postcomp F ≫ bottom Y =
    bottom X ≫ (ihom (Δ[1] : SSet.{u})).map F := by
  rw [bottom, ← Category.assoc, postcomp_inclusion]
  rw [Category.assoc, (pre squareBottomEdge).naturality F]
  rfl

lemma postcomp_right : postcomp F ≫ right Y =
    right X ≫ (ihom (Δ[1] : SSet.{u})).map F := by
  rw [right, ← Category.assoc, postcomp_inclusion]
  rw [Category.assoc, (pre squareRightEdge).naturality F]
  rfl

lemma postcomp_cofiber : postcomp F ≫ right Y ≫
      evaluateFunctorAt (Y := Y) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
    (right X ≫ evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ F := by
  rw [← Category.assoc, postcomp_right, Category.assoc, arrowMap_evaluation]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
