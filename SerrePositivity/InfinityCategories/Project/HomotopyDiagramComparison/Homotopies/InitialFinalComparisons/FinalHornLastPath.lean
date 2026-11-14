module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.InitialFinalComparisons.FinalHornKnownIntervals
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathNerve
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionFace

/-!
# 最終外側ホーンの隣接 Path と合成面

概要：元の最終外側ホーンの未知 Hom を構成するための境界データを保持する。
方針：native Path の座標面と元の面制限を使う。
規約：未知二区間を区別し、小次元の空境界も保持する。
使われ方：HTT 5.2.4.6 の相対外側ホーン充填。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open CategoryTheory.SimplicialThickening

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 最終外側ホーンの最後の隣接頂点間には内部点がない。 -/
lemma finalHornLastInterior_isEmpty (n : ℕ) :
    IsEmpty (Set.Ioo (ULift.up.{u} (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))
      (ULift.up (Fin.last (n + 2)))) := by
  constructor
  rintro ⟨j, hj, hk⟩
  have hj' : n + 1 < j.down.val := hj
  have hk' : j.down.val < n + 2 := hk
  omega

/-- 最後の隣接頂点間の native Path は一意である。 -/
lemma finalHornLastPath_eq (n : ℕ)
    (p q : SimplicialThickening.Path (ULift.up.{u} (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))
      (ULift.up (Fin.last (n + 2)))) : p = q := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathInteriorEquiv (show ULift.up.{u} (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) <
    ULift.up (Fin.last (n + 2)) from _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n)).injective
  ext j
  exact (finalHornLastInterior_isEmpty n).false j |>.elim

/-- 最後の隣接頂点間の Path の nerve は単位対象と同型である。 -/
def finalHornLastPathIso (n : ℕ) : 𝟙_ SSet.{u} ≅
    nerve (SimplicialThickening.Path (ULift.up.{u} (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))
      (ULift.up (Fin.last (n + 2)))) where
  hom :=
    { app := fun _ ↦ ↾fun _ ↦ (Functor.const _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior
        (show ULift.up.{u} (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) < ULift.up (Fin.last (n + 2))
          from _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n) ∅)
      naturality := by intros; rfl }
  inv := CartesianMonoidalCategory.toUnit _
  hom_inv_id := CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
  inv_hom_id := by
    apply CategoryTheory.NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    exact CategoryTheory.Functor.ext (fun _ ↦ finalHornLastPath_eq n _ _)

/-- 前半 Path を、penultimate を通る元の全区間の合成面と同一視する。 -/
def finalHornFrontThroughIso (n : ℕ) :
    nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))) ≅
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{u} (0 : Fin (n + 3)))
          (c := ULift.up (Fin.last (n + 2))) (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n)) : SSet) :=
  (ρ_ _).symm ≪≫ whiskerLeftIso _ (finalHornLastPathIso n) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso _ _ _

/-- 合成面との同型は最後の native Path を付加する元の豊穣合成に一致する。 -/
lemma finalHornFrontThroughIso_hom_ι (n : ℕ) :
    (finalHornFrontThroughIso.{u} n).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{u} (0 : Fin (n + 3)))
        (c := ULift.up (Fin.last (n + 2))) (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n))).ι =
      (ρ_ _).inv ≫ (_ ◁ (finalHornLastPathIso n).hom) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap _ _ _ := by
  simp only [finalHornFrontThroughIso, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso_hom_ι]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
