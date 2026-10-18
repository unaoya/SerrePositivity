module

public import SerrePositivity.KST.Comparison.FatSkeletonTail
public import SerrePositivity.KST.Comparison.FatSkeletonInvariance
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanSequentialColimitComparison

/-!
# fat realization の各行の局所化同型に対する不変性

概要：各行で局所化同型である射は fat realization 全体でも局所化同型を誘導する。
方針：有限骨格の不変性を、単射な骨格の順序列の実際の余極限へ移す。
規約：Segal 1974 Proposition 1.6 の模型の比較の補助。対角への比較は別途扱う。
使われ方：図式の射の Kan 置換などの全体への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：各行の局所化同型は fat realization 全体で局所化同型を誘導する。
方針：全ての有限骨格での比較を、骨格の単射な順序余極限へ移す。
規約：入力の各行の単射性や Kan 性は不要。
使われ方：fat realization を用いた比較の入力の置換。
-/
theorem fatRealizationMap_localized_isIso
    {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G)
    (hα : ∀ m, IsIso (AnodyneHomotopy.anodyneQ.map (α.app (op ⦋m⦌)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (fatRealizationMap α)) := by
  let β : fatSkeletonSequence F ⟶ fatSkeletonSequence G :=
    { app n := fatSkeletonMap α n
      naturality {_ _} _ := rfl }
  apply KanSequentialColimitComparison.actual_localized_isIso β ?_
    (fatSkeletonMap_localized_isIso α hα)
    (fatSkeletonCocone F) (fatSkeletonCocone G)
    (fatSkeletonCoconeIsColimit F) (fatSkeletonCoconeIsColimit G)
    (fatRealizationMap α) (fun n => (fatSkeletonMap_ι α n).symm)
  intro n
  change Mono (SSet.Subcomplex.homOfLE (fatSkeleton_monotone F (Nat.le_succ n)))
  infer_instance

end SerrePositivity.KST.Comparison
