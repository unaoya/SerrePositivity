module
public import SerrePositivity.KST.SConstruction.DoubleCofiberInputIso
public import SerrePositivity.KST.SConstruction.CutRelativeComparison
public import SerrePositivity.KST.SConstruction.CutSupportNormalization

/-! # 相対切断比較の二重 cofiber 族
概要：元の左右支持の相対 cofiber 族に完全な切断関手を適用する。
方針：cofiber 自己関手の評価の自然性と合成法則で格子の行・列を照合する。
規約：cofiber の元の全選択を保持する。使われ方：中央評価の逆同型の消滅条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 左右支持の相対 cofiber 族に元の完全な切断を適用した二重 cofiber 族。 -/
def cutDoubleCofiberFamily (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    relativeCofiberDiagrams (cutLeftSupport n k X) (cutRightSupport n k X) ⟶
      cofiberDiagrams (cofiberDiagrams (sConstruction n X.carrier)) :=
  (relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫
    cofiberEndofunctor.map (cutStableComparison n k X)).val

/-- 二重切断の行は元の外側端点を切断した cofiber 族。 -/
lemma cutDoubleCofiberFamily_row (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) (j : Fin 2) :
    doubleCofiberRow (cutDoubleCofiberFamily n k X) j =
      (relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫
        cofiberStableEvaluation (sStableModel n X)
          (stdSimplex.obj₀Equiv.symm j, stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
        cutStableComparison n k X).val := by
  have h := congrArg (fun f =>
    relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫ f)
    ((cofiberEvaluationNat
      (stdSimplex.obj₀Equiv.symm j, stdSimplex.obj₀Equiv.symm (0 : Fin 2))).naturality
        (cutStableComparison n k X))
  exact congrArg Subtype.val h

/-- 二重切断の列は元の内側端点への完全な後合成。 -/
lemma cutDoubleCofiberFamily_column (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) (j : Fin 2) :
    doubleCofiberColumn (cutDoubleCofiberFamily n k X) j =
      (relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫
        cofiberEndofunctor.map (cutStableComparison n k X ≫
          cofiberStableEvaluation (sStableModel n X)
          (stdSimplex.obj₀Equiv.symm j, stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).val := by
  have h := congrArg (fun f =>
    relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫ f)
    (cofiberEndofunctor.map_comp (cutStableComparison n k X)
      (cofiberStableEvaluation (sStableModel n X)
        (stdSimplex.obj₀Equiv.symm j, stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
  exact (congrArg Subtype.val h).symm

/-- 二重切断の一番目の行は中央評価の後の元の切断比較。 -/
lemma cutDoubleCofiberFamily_row_one (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    doubleCofiberRow (cutDoubleCofiberFamily n k X) 1 =
      (cutRelativeMiddle n k X ≫ cutStableComparison n k X).val :=
  cutDoubleCofiberFamily_row n k X 1

/-- 二重切断の一番目の列は元の相対 cofiber の包含そのもの。 -/
lemma cutDoubleCofiberFamily_column_one (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    doubleCofiberColumn (cutDoubleCofiberFamily n k X) 1 =
      (relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X)).val := by
  rw [cutDoubleCofiberFamily_column]
  change (relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X) ≫
    cofiberEndofunctor.map (cutStableComparison n k X ≫
      cofiberStableMiddle (sStableModel n X))).val = _
  rw [cutStableComparison_middle, CategoryTheory.Functor.map_id]
  exact congrArg Subtype.val (Category.comp_id
    (relativeCofiberInclusion (cutLeftSupport n k X) (cutRightSupport n k X)))

end SerrePositivity.KST.SConstruction
