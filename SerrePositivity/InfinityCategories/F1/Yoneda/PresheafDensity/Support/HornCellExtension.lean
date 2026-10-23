module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.HornCellStep

/-!
概要：一段のセル付加は元の対象の全ての指定ホーンに充填を与える。
方針：指定されたホーン射で添字付けた標準単体のコピーを実際に含める。
規約：元のホーン射を単位射で送ったものと境界で厳密に一致する。
使われ方：セル付加の反復の余極限が Kan となることの入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の対象の指定ホーンは一段の付加後に元の境界を保って充填できる。
方針：対応するセルのコピーを二重の余積へ含め、pushout の可換性を使う。
規約：n+1 次元の全てのホーンを扱う。
使われ方：明示的な Kan 置換の反復で必要な一段先の充填。 -/
lemma exists_hornCellStep_extension {X : SSet.{u}} {n : ℕ} {i : Fin (n + 2)}
    (t : (horn (n + 1) i : SSet.{u}) ⟶ X) :
    ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ hornCellStep.obj X,
      (horn (n + 1) i).ι ≫ F = t ≫ hornCellStepUnit.app X := by
  let S := fun h : Σ m : ℕ, Fin (m + 2) ↦
    cellCopiesFunctor (horn (h.1 + 1) h.2 : SSet.{u}) (horn (h.1 + 1) h.2)
  let T := fun h : Σ m : ℕ, Fin (m + 2) ↦
    cellCopiesFunctor (horn (h.1 + 1) h.2 : SSet.{u}) Δ[h.1 + 1]
  let a := Sigma.ι (fun _ : (horn (n + 1) i : SSet.{u}) ⟶ X ↦ (horn (n + 1) i : SSet.{u})) t
  let b := Sigma.ι (fun _ : (horn (n + 1) i : SSet.{u}) ⟶ X ↦ (Δ[n + 1] : SSet.{u})) t
  let jS := (Sigma.ι S ⟨n, i⟩).app X
  let jT := (Sigma.ι T ⟨n, i⟩).app X
  let m := (cellCopiesMap (horn (n + 1) i) (horn (n + 1) i).ι).app X
  have he : jS ≫ hornCopiesEvaluation.{u}.app X =
      (cellCopiesEvaluation (horn (n + 1) i : SSet.{u})).app X :=
    NatTrans.congr_app (Sigma.ι_comp_desc
      (fun h : Σ m : ℕ, Fin (m + 2) ↦ cellCopiesEvaluation.{u} (horn (h.1 + 1) h.2))
      ⟨n, i⟩) X
  have hm : jS ≫ hornCopiesBoundary.app X = m ≫ jT :=
    NatTrans.congr_app (Sigma.ι_map
      (fun h : Σ m : ℕ, Fin (m + 2) ↦
        cellCopiesMap.{u} (horn (h.1 + 1) h.2) (horn (h.1 + 1) h.2).ι) ⟨n, i⟩) X
  have hc := NatTrans.congr_app hornCellStep_condition.{u} X
  refine ⟨b ≫ jT ≫ hornCellStepCells.app X, ?_⟩
  calc
    (horn (n + 1) i).ι ≫ b ≫ jT ≫ hornCellStepCells.app X =
        a ≫ m ≫ jT ≫ hornCellStepCells.app X := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ jT ≫ hornCellStepCells.app X) (cellCopiesMap_ι _ t).symm
    _ = a ≫ jS ≫ hornCopiesBoundary.app X ≫ hornCellStepCells.app X := by
      simpa only [Category.assoc] using congrArg (fun z ↦ a ≫ z ≫ hornCellStepCells.app X)
        hm.symm
    _ = a ≫ jS ≫ hornCopiesEvaluation.app X ≫ hornCellStepUnit.app X := by
      simpa only [NatTrans.comp_app, Category.assoc] using congrArg (fun z ↦ a ≫ jS ≫ z) hc.symm
    _ = t ≫ hornCellStepUnit.app X := by
      rw [← Category.assoc jS, he, ← Category.assoc a, cellCopiesEvaluation_ι]

end SerrePositivity.InfinityCategories.F2
