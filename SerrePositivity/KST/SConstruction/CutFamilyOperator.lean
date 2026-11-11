module
public import SerrePositivity.KST.SConstruction.ArCutEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InternalHomSwap

/-! # 切断 cofiber 族の単体的作用素
概要：切断を個々の図式だけでなく、S_n C の全単体の coherent な族に適用する。
方針：添字の前合成と内部 currying を合成し、全頂点で cofiber 条件を持ち上げる。
規約：全高次単体と元の図式内の選択を保持する。使われ方：切断比較の完全関手化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 切断四角形の族を作る前合成と内部 currying の作用素。 -/
def cutDiagramFamilyOperator (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u}) :
    (ihom (arNerve n)).obj C ⟶ (ihom (arNerve n)).obj
      ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) :=
  (pre ((β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n)).hom ≫ arCutSquareMap n k)).app C ≫
    (ihomCurryIso (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n) C).hom

/-- 全 gapped 図式の切断四角形の族を取る作用素。 -/
def cutRawFamilyOperator (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u}) :
    sConstruction n C ⟶ (ihom (arNerve n)).obj
      ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) :=
  (gappedSubcomplex n C).ι ≫ cutDiagramFamilyOperator n k C

/-- 切断作用素の頂点は元の図式の実際の切断四角形の族。 -/
lemma cutRawFamilyOperator_vertex (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u})
    (v : (sConstruction n C) _⦋0⦌) :
    (cutRawFamilyOperator n k C).app (Opposite.op ⦋0⦌) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (arCutFamily k (gappedDiagram v)) := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram v) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).apply_symm_apply v.val
  change ((pre ((β_ (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n)).hom ≫
      arCutSquareMap n k)).app C ≫ ihomCurry (Δ[1] ⊗ Δ[1] : SSet.{u}) (arNerve n) C).app
        (Opposite.op ⦋0⦌) v.val = _
  rw [← hv]
  rfl

/-- 作用素の uncurry は全頂点で実際の cofiber 四角形を値に持つ。 -/
lemma cutRawFamilyOperator_isCofiber (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u})
    [Quasicategory C] (s : (arNerve n ⊗ sConstruction n C) _⦋0⦌) :
    IsCofiberDiagramVertex
      ((uncurry (cutRawFamilyOperator n k C)).app (Opposite.op ⦋0⦌) s) := by
  rcases s with ⟨a, v⟩
  change IsCofiberDiagramVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a).app (Opposite.op ⦋0⦌)
    ((cutRawFamilyOperator n k C).app (Opposite.op ⦋0⦌) v))
  rw [cutRawFamilyOperator_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
    ((gappedCutCofiberFamily k (gappedDiagram_isGapped v)).app (Opposite.op ⦋0⦌) a)

/-- 全ての入力の高次単体に作用する、全 cofiber 図式値の切断族。 -/
def cutCofiberFamilyOperator (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u}) [Quasicategory C] :
    sConstruction n C ⟶ (ihom (arNerve n)).obj (cofiberDiagrams C) :=
  curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsCofiberDiagramVertex (uncurry (cutRawFamilyOperator n k C))
    (cutRawFamilyOperator_isCofiber n k C))

/-- 切断の cofiber 族の作用素は包含後に元の全単体の族を保持する。 -/
lemma cutCofiberFamilyOperator_ι (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u}) [Quasicategory C] :
    cutCofiberFamilyOperator n k C ≫
      (ihom (arNerve n)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
        cutRawFamilyOperator n k C := by
  apply uncurry_injective
  rw [uncurry_natural_right, cutCofiberFamilyOperator, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]

end SerrePositivity.KST.SConstruction
