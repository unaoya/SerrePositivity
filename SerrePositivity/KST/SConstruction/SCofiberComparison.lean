module
public import SerrePositivity.KST.SConstruction.SCofiberPointwise
public import SerrePositivity.InfinityCategories.Kan.SwapEvaluation

/-! # S 構成と cofiber 図式の交換比較
概要：cofiber 値の gapped 図式を、gapped 図式を値とする cofiber 四角形へ送る。
方針：零角と押し出しを全 Ar 成分で判定する。
規約：元の四角形と全ての角の評価を保持する。使われ方：有限反復の加法性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 各頂点の転置した四角形を gapped 包含へ送ると元の族の転置となる。 -/
lemma sCofiberTransposeSquare_vertex_ι (n : ℕ) (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (v : (sConstruction n (cofiberDiagrams C)) _⦋0⦌) :
    squareDiagram ((sCofiberTransposeSquare n C).app (Opposite.op ⦋0⦌) v) ≫
      (gappedSubcomplex n C).ι =
      internalHomFlipHomEquiv (arNerve n) (Δ[1] ⊗ Δ[1] : SSet.{u}) C
        (gappedDiagram v ≫ (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sCofiberTransposeSquare_ι n C) (Opposite.op ⦋0⦌)) v
  change ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map (gappedSubcomplex n C).ι).app
    (Opposite.op ⦋0⦌) ((sCofiberTransposeSquare n C).app (Opposite.op ⦋0⦌) v) = _ at h
  apply (functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u})
    ((ihom (arNerve n)).obj C)).injective
  change ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map (gappedSubcomplex n C).ι).app
    (Opposite.op ⦋0⦌)
      (functorVertex (squareDiagram ((sCofiberTransposeSquare n C).app
        (Opposite.op ⦋0⦌) v))) = _
  rw [show functorVertex (squareDiagram ((sCofiberTransposeSquare n C).app
      (Opposite.op ⦋0⦌) v)) = (sCofiberTransposeSquare n C).app (Opposite.op ⦋0⦌) v from
    (functorVertexEquiv _ _).apply_symm_apply _]
  exact h.trans (sCofiberRawTranspose_vertex n C v)

/-- 転置した四角形は S_n C の内部で実際の cofiber 四角形。 -/
lemma sCofiberTransposeSquare_isCofiber (n : ℕ) (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (v : (sConstruction n (cofiberDiagrams C)) _⦋0⦌) :
    IsCofiberDiagramVertex ((sCofiberTransposeSquare n C).app (Opposite.op ⦋0⦌) v) := by
  apply (gappedSquare_cofiber_iff_pointwise _).2
  intro a
  rw [← Category.assoc, sCofiberTransposeSquare_vertex_ι, flipFamily_evaluate]
  exact fullSubcomplexOnVertices_vertex ((gappedDiagram v).app (Opposite.op ⦋0⦌) a)

/-- 全 cofiber 値の S_n 図式と S_n 値の cofiber 図式の交換。 -/
def sCofiberComparison (n : ℕ) (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    sConstruction n (cofiberDiagrams C) ⟶ cofiberDiagrams (sConstruction n C) :=
  fullSubcomplexLift _ (sCofiberTransposeSquare n C) (sCofiberTransposeSquare_isCofiber n C)

/-- 交換比較の包含後の射は構成した四角形の転置そのもの。 -/
lemma sCofiberComparison_ι (n : ℕ) (C : SSet.{u}) [Quasicategory C] [IsStable C] :
    sCofiberComparison n C ≫ (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
      sCofiberTransposeSquare n C := fullSubcomplexLift_ι _ _ _

/-- 交換比較の各角は元の完全な評価に S_n を適用した射と厳密に一致する。 -/
lemma sCofiberComparison_evaluation (n : ℕ) (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (q : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌) :
    sCofiberComparison n C ≫ (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
      evaluateFunctorAt q =
    sPostcompCofiber n
      ((fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ evaluateFunctorAt (Y := C) q)
      (cofiberEvaluation_preservesSConstructionData C q).toCofiberData := by
  rw [← Category.assoc, sCofiberComparison_ι]
  apply (cancel_mono (gappedSubcomplex n C).ι).1
  rw [Category.assoc, ← ihom_postcomp_evaluate, ← Category.assoc,
    sCofiberTransposeSquare_ι, sCofiberRawTranspose, Category.assoc, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kan.internalHomSwap_evaluate_right, ← Functor.map_comp,
    sPostcompCofiber_ι]
  rfl

end SerrePositivity.KST.SConstruction
