module
public import SerrePositivity.KST.SConstruction.CutDoubleCofiberFamily

/-! # 左右支持による二重切断格子の消滅条件
概要：二重切断格子の零番目の行・列の商が、反対側の支持条件により零となる。
方針：元の二評価の自然性と切断の全角の厳密な式で実際の商を計算する。
規約：消滅を追加入力にしない。使われ方：中央評価の coherent な逆同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 二重切断の零番目の行の商は元の subobject の右切断。 -/
lemma cutDoubleCofiberFamily_row_zero_quotient (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    doubleCofiberRow (cutDoubleCofiberFamily n k X) 0 ≫ cofiberApex (sConstruction n X.carrier) =
      ((relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫
        cofiberStableSubobject (sStableModel n X)).val) ≫
        sMap X.carrier (cutCornerOrder k 1 1) := by
  rw [cutDoubleCofiberFamily_row]
  change (relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫
    cofiberStableSubobject (sStableModel n X) ≫ cutStableComparison n k X ≫
      cofiberStableQuotient (sStableModel n X)).val = _
  exact congrArg Subtype.val
    (congrArg (fun f : sStableModel n X ⟶ sStableModel n X =>
      relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫
        cofiberStableSubobject (sStableModel n X) ≫ f)
      (cutStableComparison_evaluation n k X 1 1))

/-- 二重切断の零番目の列の商は元の quotient の左切断。 -/
lemma cutDoubleCofiberFamily_column_zero_quotient (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    doubleCofiberColumn (cutDoubleCofiberFamily n k X) 0 ≫ cofiberApex (sConstruction n X.carrier) =
      ((relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫
        cofiberStableQuotient (sStableModel n X)).val) ≫ sMap X.carrier (cutCornerOrder k 0 0) := by
  rw [cutDoubleCofiberFamily_column]
  change (relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫
    cofiberEndofunctor.map (cutStableComparison n k X ≫ cofiberStableSubobject (sStableModel n X)) ≫
      cofiberStableQuotient (sStableModel n X)).val = _
  have h₁ := congrArg (fun f =>
    relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫ f)
    (cofiberQuotientNat.naturality
      (cutStableComparison n k X ≫ cofiberStableSubobject (sStableModel n X)))
  have h₂ := congrArg (fun f : sStableModel n X ⟶ sStableModel n X =>
    relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫
      cofiberStableQuotient (sStableModel n X) ≫ f)
    (cutStableComparison_evaluation n k X 0 0)
  exact congrArg Subtype.val (h₁.trans h₂)

/-- 相対入力の左右支持により、二重切断格子の零番目の行の商は全点で実際に零。 -/
lemma cutDoubleCofiberFamily_row_zero_isZero (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u})
    (v : (relativeCofiberDiagrams (cutLeftSupport n k X) (cutRightSupport n k X)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((doubleCofiberRow (cutDoubleCofiberFamily n k X) 0 ≫
      cofiberApex (sConstruction n X.carrier)).app (Opposite.op ⦋0⦌) v) := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌) v)
    (cutDoubleCofiberFamily_row_zero_quotient n k X)
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex h).mpr
    (cutLeftSupport_rightCut_isZero n k X _
      (relativeCofiber_vertex (cutLeftSupport n k X) (cutRightSupport n k X) v).1)

/-- 相対入力の左右支持により、二重切断格子の零番目の列の商は全点で実際に零。 -/
lemma cutDoubleCofiberFamily_column_zero_isZero (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u})
    (v : (relativeCofiberDiagrams (cutLeftSupport n k X) (cutRightSupport n k X)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((doubleCofiberColumn (cutDoubleCofiberFamily n k X) 0 ≫
      cofiberApex (sConstruction n X.carrier)).app (Opposite.op ⦋0⦌) v) := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌) v)
    (cutDoubleCofiberFamily_column_zero_quotient n k X)
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex h).mpr
    (cutRightSupport_leftCut_isZero n k X _
      (relativeCofiber_vertex (cutLeftSupport n k X) (cutRightSupport n k X) v).2)

end SerrePositivity.KST.SConstruction
