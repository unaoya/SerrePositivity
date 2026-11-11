module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.PartialTower
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.SequencePrepend
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.SmallSemifree
public import SerrePositivity.DifferentialGraded.Module.Disk
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution

/-!
概要：部分 cell 列の strict 余極限に、実 semifree filtration を与える。
方針：初期 disk 層を二つの sphere 層へ分け、各 cone 商を shifted sphere で表示する。
規約：各自由層の添字は選択された実セルである。
使われ方：D-8 d の κ-small な各段の代表化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : ModuleCategory R D) (s : Set (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaResolutionLabel R D M))
  (hs : ∀ a ∈ s, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDependencies R D M a ⊆ s)

def dgKappaPartialDiskUpper : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDiskSelection R D M s → ModuleCategory R D :=
  fun j => freeSphere R D j.val.1 (j.val.2.1 + 1)

def dgKappaPartialDiskLower : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDiskSelection R D M s → ModuleCategory R D :=
  fun j => freeSphere R D j.val.1 j.val.2.1

def dgKappaPartialDiskBoundary :
    (∐ dgKappaPartialDiskUpper R D M s) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionObject R D M s hs 0 :=
  Limits.Sigma.map (fun j : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDiskSelection R D M s =>
    freeCellBoundary R D j.val.1 j.val.2.1)

def dgKappaPartialDiskQuotient :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionObject R D M s hs 0 ⟶ ∐ dgKappaPartialDiskLower R D M s :=
  Limits.Sigma.map (fun j : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDiskSelection R D M s =>
    freeDiskToSphere R D j.val.1 j.val.2.1)

def dgKappaPartialDiskSplit : ModuleGradedSplit R D
    (dgKappaPartialDiskBoundary R D M s hs) (dgKappaPartialDiskQuotient R D M s hs) :=
  moduleCoproductGradedSplit R D _ _
    (fun j : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDiskSelection R D M s => freeDiskGradedSplit R D j.val.1 j.val.2.1)

def dgKappaPartialSemifreeStage : ℕ → ModuleCategory R D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPrependObject (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionObject R D M s hs)
    (B := ∐ dgKappaPartialDiskUpper R D M s)

def dgKappaPartialSemifreeTransition : ∀ n,
    dgKappaPartialSemifreeStage R D M s hs n ⟶ dgKappaPartialSemifreeStage R D M s hs (n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPrependTransition (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionTransition R D M s hs)
    (dgKappaPartialDiskBoundary R D M s hs)

def dgKappaPartialSemifreeQuotient : ℕ → ModuleCategory R D
  | 0 => ∐ dgKappaPartialDiskLower R D M s
  | n + 1 => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModule R D
      (moduleKernelCellFamily R D (moduleResolutionStage R D M n).hom)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M s n))⟦(1 : ℤ)⟧

def dgKappaPartialSemifreeQuotientMap : ∀ n,
    dgKappaPartialSemifreeStage R D M s hs (n + 1) ⟶ dgKappaPartialSemifreeQuotient R D M s n
  | 0 => dgKappaPartialDiskQuotient R D M s hs
  | n + 1 => moduleConeConnecting R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialAttachment R D M s hs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs n))

def dgKappaPartialSemifreeSplit (n : ℕ) : ModuleGradedSplit R D
    (dgKappaPartialSemifreeTransition R D M s hs n)
    (dgKappaPartialSemifreeQuotientMap R D M s hs n) :=
  match n with
  | 0 => dgKappaPartialDiskSplit R D M s hs
  | n + 1 => moduleConeGradedSplit R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialAttachment R D M s hs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs n))

def dgKappaPartialSemifreeInitial :
    ModuleSphereFreePresentation R D (dgKappaPartialSemifreeStage R D M s hs 0) where
  Index := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDiskSelection R D M s
  object := fun j => j.val.1
  degree := fun j => j.val.2.1 + 1
  iso := Iso.refl _

def dgKappaPartialSemifreeQuotientPresentation (n : ℕ) :
    ModuleSphereFreePresentation R D (dgKappaPartialSemifreeQuotient R D M s n) := by
  cases n with
  | zero => exact
      { Index := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDiskSelection R D M s
        object := fun j => j.val.1
        degree := fun j => j.val.2.1
        iso := Iso.refl _ }
  | succ n => exact
      { Index := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M s n
        object := fun j => j.val.1
        degree := fun j => j.val.2.1
        iso := moduleShiftCoproductIso R D _ 1 ≪≫ Sigma.mapIso
          (fun j : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M s n =>
            freeSphereShiftIso R D j.val.1 (j.val.2.1 + 1) 1 ≪≫
              eqToIso (congrArg (freeSphere R D j.val.1) (by omega))) }

def dgKappaPartialSemifreeFiltration :
    ModuleSemifreeFiltration R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolution R D M s hs) where
  stage := dgKappaPartialSemifreeStage R D M s hs
  transition := dgKappaPartialSemifreeTransition R D M s hs
  initial := dgKappaPartialSemifreeInitial R D M s hs
  quotient := dgKappaPartialSemifreeQuotient R D M s
  quotientMap := dgKappaPartialSemifreeQuotientMap R D M s hs
  split := dgKappaPartialSemifreeSplit R D M s hs
  quotientPresentation := dgKappaPartialSemifreeQuotientPresentation R D M s
  cocone := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPrependCocone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionTransition R D M s hs)
    (dgKappaPartialDiskBoundary R D M s hs)
    (colimit.cocone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionDiagram R D M s hs))
  isColimit := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPrependIsColimit _ _ (colimit.isColimit _)
  iso := Iso.refl _

lemma dgKappaPartialResolution_representativeCovers {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular) (hsmall : HasCardinalLT s κ) :
    ∃ N : ModuleCategory R D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ N ∧
      Nonempty ((moduleToHomotopy R D).obj N ≅
        (moduleToHomotopy R D).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolution R D M s hs)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaClosedProjectiveObjects_smallSemifreeCovers R D hκ hreg
    (dgKappaPartialSemifreeFiltration R D M s hs)
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDiskSelection_small R D M hsmall
  · intro n
    cases n with
    | zero => exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDiskSelection_small R D M hsmall
    | succ n => exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection_small R D M hsmall n

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
