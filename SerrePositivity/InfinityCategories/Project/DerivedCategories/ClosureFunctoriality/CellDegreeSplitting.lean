module
public import SerrePositivity.DifferentialGraded.Resolution.Cell
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
概要：標準 cell 分解の段零包含を各次数で分裂させる。
方針：cell 付加の空語射影を各次数で反復し、余極限の普遍性で貼り合わせる。
規約：分裂は次数ごとの加群射。微分と可換するとは主張しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory Limits MonoidalCategory DifferentialGraded HomologicalComplex
open DGCategoryCellResolution
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 追加 cell の空語射影。内部微分に対する複体射として定義する。 -/
def dgCellEmptyProjection {I : Type w} [Small.{u} I]
    (C : DGCellAttachment.Family R D I) (x y : D) :
    C.internalHom R D I x y ⟶ homObject R D x y :=
  Sigma.desc (fun w => match w with
    | [] => 𝟙 _
    | _ :: _ => 0)

lemma dgCellEmptyProjection_split {I : Type w} [Small.{u} I]
    (C : DGCellAttachment.Family R D I) (x y : D) :
    C.originalHom R D I x y ≫ dgCellEmptyProjection R D C x y = 𝟙 _ :=
  Sigma.ι_desc _ _

/-- 一回の cell 付加における、追加した生成元を捨てる次数別射影。 -/
def dgCellTransitionRetraction (n : ℕ) (x y : D) (i : ℤ) :
    (stageHom R D (n + 1) x y).X i ⟶ (stageHom R D n x y).X i :=
  (@dgCellEmptyProjection R _ D (stage R D n).category
    (stage R D n).CellIndex inferInstance (stage R D n).cells x y).f i

lemma dgCellTransitionRetraction_split (n : ℕ) (x y : D) (i : ℤ) :
    (transition R D n x y).f i ≫ dgCellTransitionRetraction R D n x y i = 𝟙 _ := by
  exact congrArg (fun f => f.f i)
    (@dgCellEmptyProjection_split R _ D (stage R D n).category inferInstance
      (stage R D n).CellIndex inferInstance (stage R D n).cells x y)

/-- 各段から段零への次数別射影。 -/
def dgCellStageZeroProjection (x y : D) (i : ℤ) : (n : ℕ) →
    (stageHom R D n x y).X i ⟶ (stageHom R D 0 x y).X i
  | 0 => 𝟙 _
  | n + 1 => dgCellTransitionRetraction R D n x y i ≫ dgCellStageZeroProjection x y i n

lemma dgCellStageZeroProjection_transition (x y : D) (i : ℤ) (n : ℕ) :
    (transition R D n x y).f i ≫ dgCellStageZeroProjection R D x y i (n + 1) =
      dgCellStageZeroProjection R D x y i n := by
  rw [dgCellStageZeroProjection, ← Category.assoc, dgCellTransitionRetraction_split,
    Category.id_comp]

/-- 複体余極限の各次数から初期段への射影 cocone。 -/
def dgCellStageZeroCocone (x y : D) (i : ℤ) :
    Cocone (homDiagram R D x y ⋙ HomologicalComplex.eval (ModuleCat R) (.up ℤ) i) where
  pt := (stageHom R D 0 x y).X i
  ι := NatTrans.ofSequence (fun n => dgCellStageZeroProjection R D x y i n) (fun n => by
    change ((homDiagram R D x y).map (homOfLE (Nat.le_succ n))).f i ≫ _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
    dsimp only [homDiagram]
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact dgCellStageZeroProjection_transition R D x y i n)

/-- 最終分解から初期段への次数別射影。 -/
def dgCellStageZeroRetraction (x y : D) (i : ℤ) :
    (candidateHom R D x y).X i ⟶ (stageHom R D 0 x y).X i :=
  (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat R) (.up ℤ) i)
    (colimit.isColimit (homDiagram R D x y))).desc (dgCellStageZeroCocone R D x y i)

lemma dgCellStageZeroRetraction_split (x y : D) (i : ℤ) :
    (stageInclusion R D 0 x y).f i ≫ dgCellStageZeroRetraction R D x y i = 𝟙 _ :=
  (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat R) (.up ℤ) i)
    (colimit.isColimit (homDiagram R D x y))).fac (dgCellStageZeroCocone R D x y i) 0

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
