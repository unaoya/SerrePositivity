module
public import SerrePositivity.KST.Fibration.SStageKernelPredicate
public import SerrePositivity.KST.Fibration.VerdierKernelEquivalence
public import SerrePositivity.KST.SConstruction.StableModelEquivalences

/-! # 元の Verdier 包含の S_n と、同じ S 後合成の実核との全写像空間での比較

K-1 の閉じた部分圏との交換同型と、元の核同値の S_n を合成する。
S_n 商の局所化普遍性は別入力であり、ここから結論しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ)

/-- 元の S_n(D) を、同じ S_n(B) 内の全核図式へ送る全写像空間の同値。 -/
def verdierSStageKernelEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (sConstruction n A.obj)
      (closedSubcategory (sClosedPredicate n (kernelClosedPredicate q))) :=
  ((verdierKernelEquivalence h).sConstruction n).toQCatEquivalence.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (sClosedIso n (kernelClosedPredicate q)))

/-- 同じ核比較の包含後は、元の Verdier 包含による S 後合成そのもの。 -/
theorem verdierSStageKernelEquivalence_inclusion :
    (verdierSStageKernelEquivalence h n).hom ≫
      (closedStableInclusion (sClosedPredicate n (kernelClosedPredicate q))).val =
        sPostcomp n i.hom (exactMap_preservesSData i) := by
  have he : verdierKernelExact h ≫ closedStableInclusion (kernelClosedPredicate q) =
      sInputExactMap i := Subtype.ext (verdierKernelExact_ι h)
  have hm := congrArg (fun f => ((sEndofunctor n).map f).val) he
  rw [Functor.map_comp] at hm
  have hs := congrArg
    (fun f : sConstruction n (closedSubcategory (kernelClosedPredicate q)) ⟶
        sConstruction n B.obj => ((sEndofunctor n).map (verdierKernelExact h)).val ≫ f)
    (sClosedComparison_inclusion n (kernelClosedPredicate q))
  exact hs.trans hm

end SerrePositivity.KST.Fibration
