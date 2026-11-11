module
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Module.Graded
public import Mathlib.Logic.Small.Basic
public import SerrePositivity.DifferentialGraded.Module.ActionLimits

/-!
概要：元の semifree filtration の実初期層と各商から、cell の小さいラベルを取り出す。
方針：sphere 表示のラベルを可算和し、元の全次数分裂を使った graded 包含を保持する。
規約：graded 包含を閉射と呼ばない。使われ方：cell 微分の下位層への依存先の抽出。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {M : ModuleCategory R D} (F : ModuleSemifreeFiltration R D M)

abbrev DGKappaSemifreeRawCell :=
  Sum F.initial.Index (Σ n : ℕ, (F.quotientPresentation n).Index)

instance dgKappaSemifreeRawCell_small : Small.{u} (DGKappaSemifreeRawCell R D F) := by
  let : Small.{u} F.initial.Index := F.initial.smallIndex
  let : ∀ n, Small.{u} (F.quotientPresentation n).Index :=
    fun n => (F.quotientPresentation n).smallIndex
  dsimp [DGKappaSemifreeRawCell]
  infer_instance

abbrev DGKappaSemifreeCell := Shrink.{u} (DGKappaSemifreeRawCell R D F)

def dgKappaSemifreeCellObject : DGKappaSemifreeRawCell R D F → D
  | .inl a => F.initial.object a
  | .inr ⟨n, a⟩ => (F.quotientPresentation n).object a

def dgKappaSemifreeCellDegree : DGKappaSemifreeRawCell R D F → ℤ
  | .inl a => F.initial.degree a
  | .inr ⟨n, a⟩ => (F.quotientPresentation n).degree a

def dgKappaSemifreeCellHeight : DGKappaSemifreeRawCell R D F → ℕ
  | .inl _ => 0
  | .inr ⟨n, _⟩ => n + 1

abbrev dgKappaSemifreeCellSphere (a : DGKappaSemifreeRawCell R D F) :=
  freeSphere R D (dgKappaSemifreeCellObject R D F a) (dgKappaSemifreeCellDegree R D F a)

/-- 元の filtration の選んだ層から最終加群への同じ閉包含。 -/
def dgKappaSemifreeStageToModule (n : ℕ) : F.stage n ⟶ M := F.cocone.ι.app n ≫ F.iso.hom

/-- 実閉射を同じ主 Hom end の閉次数零要素として読む。 -/
def dgKappaClosedModuleElement {P Q : ModuleCategory R D} (f : P ⟶ Q) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) P)
      (ForgetEnrichment.to (Complex R) Q)).X 0 :=
  (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val

/-- 各 cell の元の graded 包含。正の高さでは differential と可換とは主張しない。 -/
def dgKappaSemifreeCellInclusion (a : DGKappaSemifreeRawCell R D F) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (dgKappaSemifreeCellSphere R D F a))
      (ForgetEnrichment.to (Complex R) M)).X 0 := by
  let : Small.{u} F.initial.Index := F.initial.smallIndex
  let : ∀ n, Small.{u} (F.quotientPresentation n).Index :=
    fun n => (F.quotientPresentation n).smallIndex
  cases a with
  | inl a =>
    exact dgKappaClosedModuleElement R D
      (Sigma.ι (fun a => freeSphere R D (F.initial.object a) (F.initial.degree a)) a ≫
        F.initial.iso.inv ≫ dgKappaSemifreeStageToModule R D F 0)
  | inr a =>
    obtain ⟨n, a⟩ := a
    let g := Sigma.ι (fun a => freeSphere R D ((F.quotientPresentation n).object a)
      ((F.quotientPresentation n).degree a)) a ≫ (F.quotientPresentation n).iso.inv
    exact compose R (D := RightModule R D) (dgKappaClosedModuleElement R D (dgKappaSemifreeStageToModule R D F (n + 1)))
      (compose R (D := RightModule R D) (F.split n).sectionElement (dgKappaClosedModuleElement R D g) (zero_add 0))
      (zero_add 0)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
