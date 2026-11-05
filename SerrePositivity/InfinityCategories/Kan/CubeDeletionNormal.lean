module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.CubeThreeStageNormalForm

/-! # 削除語の標準的な保持・削除表示
概要：元の各入力を右端から一度ずつ保持または削除する標準表示を作る。
方針：入力次元で帰納し、保持する入力の順序つき添字を回収する。
規約：右端の入力が座標零。使われ方：削除語の Serre 評価の表示非依存性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction

/-- 各入力を右端から保持または削除する標準表示。 -/
inductive CubeDeletionNormal : ℕ → ℕ → Type
  | nil : CubeDeletionNormal 0 0
  | drop {n m : ℕ} (d : CubeDeletionNormal n m) : CubeDeletionNormal (n + 1) m
  | keep {n m : ℕ} (d : CubeDeletionNormal n m) : CubeDeletionNormal (n + 1) (m + 1)

/-- 標準表示が保持する元の入力座標。 -/
def cubeDeletionNormalEmbedding : {n m : ℕ} → CubeDeletionNormal n m → (Fin m → Fin n)
  | _, _, .nil => Fin.elim0
  | _, _, .drop d => fun i => (cubeDeletionNormalEmbedding d i).succ
  | _, _, .keep d => Fin.cons 0 (fun i => (cubeDeletionNormalEmbedding d i).succ)

/-- 全入力を保持する標準表示。 -/
def cubeDeletionNormalId : (n : ℕ) → CubeDeletionNormal n n
  | 0 => .nil
  | n + 1 => .keep (cubeDeletionNormalId n)

/-- 全入力を保持する標準表示の添字は恒等。 -/
lemma cubeDeletionNormalId_embedding (n : ℕ) :
    cubeDeletionNormalEmbedding (cubeDeletionNormalId n) = _root_.id := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [cubeDeletionNormalId, cubeDeletionNormalEmbedding]
    · simp [cubeDeletionNormalId, cubeDeletionNormalEmbedding, ih]

/-- 一つの出力を削除して同じ保持・削除表示へ戻す。 -/
def cubeDeletionNormalErase : {n m : ℕ} → CubeDeletionNormal n (m + 1) →
    Fin (m + 1) → CubeDeletionNormal n m
  | _, _, .drop d, i => .drop (cubeDeletionNormalErase d i)
  | _, 0, .keep d, _ => .drop d
  | _, _ + 1, .keep d, i =>
      Fin.cases (.drop d) (fun j => .keep (cubeDeletionNormalErase d j)) i

/-- 標準表示からの一出力削除は、元の選択添字から同じ座標を飛ばすこと。 -/
lemma cubeDeletionNormalErase_embedding {n m : ℕ} (d : CubeDeletionNormal n (m + 1))
    (i : Fin (m + 1)) :
    cubeDeletionNormalEmbedding (cubeDeletionNormalErase d i) =
      cubeDeletionNormalEmbedding d ∘ i.succAbove := by
  induction n generalizing m with
  | zero => cases d
  | succ n ih =>
    cases d with
    | drop d =>
      funext j
      exact congrArg Fin.succ (congrFun (ih d i) j)
    | keep d =>
      cases m with
      | zero => funext j; exact Fin.elim0 j
      | succ m =>
        refine Fin.cases ?_ (fun i => ?_) i
        · funext j
          simp [cubeDeletionNormalErase, cubeDeletionNormalEmbedding]
        · funext j
          refine Fin.cases ?_ (fun j => ?_) j
          · simp [cubeDeletionNormalErase, cubeDeletionNormalEmbedding]
          · simpa [cubeDeletionNormalErase, cubeDeletionNormalEmbedding] using
              congrArg Fin.succ (congrFun (ih d i) j)

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalEmbedding := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalErase (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalErase := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalErase

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalErase_embedding := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalErase_embedding

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalId (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalId := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalId

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalId_embedding := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalId_embedding

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.below (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.below := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.below

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.brecOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.brecOn := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.brecOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.casesOn := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.ctorElim (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.ctorElim := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.ctorElim

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.ctorElimType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.ctorElimType := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.ctorElimType

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.ctorIdx := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.drop (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.drop := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.drop

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.keep (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.keep := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.keep

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.nil (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.nil := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.nil

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.noConfusionType := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.rec := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.recOn := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding._f (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalEmbedding._f := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding._f

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalEmbedding._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding._sunfold (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalEmbedding._sunfold := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding._sunfold

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding._unsafe_rec (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalEmbedding._unsafe_rec := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding._unsafe_rec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalEmbedding.eq_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalEmbedding.eq_2 := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding.eq_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalEmbedding.eq_3 := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding.eq_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalEmbedding.eq_def := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding.eq_def

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding.match_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalEmbedding.match_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalEmbedding.match_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalErase._f (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalErase._f := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalErase._f

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalErase._sunfold (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalErase._sunfold := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalErase._sunfold

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalErase._unsafe_rec (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalErase._unsafe_rec := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalErase._unsafe_rec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalErase.eq_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalErase.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalErase.eq_2 := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalErase.eq_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalErase.eq_3 := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalErase.eq_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalErase.eq_def := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalErase.eq_def

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalErase.match_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalErase.match_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalErase.match_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalId._f (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalId._f := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalId._f

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalId._sunfold (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalId._sunfold := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalId._sunfold

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalId._unsafe_rec (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalId._unsafe_rec := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalId._unsafe_rec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalId.eq_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalId.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalId.eq_2 := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalId.eq_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalId.eq_def := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalId.eq_def

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalId.match_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionNormalId.match_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeDeletionNormalId.match_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.brecOn.eq := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.brecOn.eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.brecOn.go (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.brecOn.go := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.brecOn.go

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.drop.elim (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.drop.elim := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.drop.elim

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.drop.inj := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.drop.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.drop.injEq := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.drop.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.drop.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.drop.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.drop.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.drop.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.drop.sizeOf_spec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.keep.elim (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.keep.elim := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.keep.elim

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.keep.inj := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.keep.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.keep.injEq := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.keep.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.keep.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.keep.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.keep.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.keep.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.keep.sizeOf_spec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.nil.elim (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.nil.elim := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.nil.elim

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionNormal.nil.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionNormal.nil.sizeOf_spec
