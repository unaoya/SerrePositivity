module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveHornCorner
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.NativeWeightedSections
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedExtensions

/-!
概要：元の重み制限の全境界の持ち上げを、同じ相対テンソルの延長へ転置する。
方針：既存のweightedCornerの二射の押し出しと元のcurry・uncurryを使う。
規約：IS-W2 R03a.1の既存の延長法則の証明分割。
使われ方：各値がKanの係数に対する射影anodyneな重み制限。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open scoped _root_.Simplicial _root_.SSet.modelCategoryQuillen
variable {I : Type u} [SmallCategory I]

/-- 同じ相対テンソルの延長から、元の切断制限の全境界の持ち上げを得る。 -/
theorem weightedSectionsPre_trivialKanFibration_of_corner_extensions
    {W W' H : I ⥤ SSet.{u}} (j : W ⟶ W')
    (hcorner : ∀ n, ∀ a : (weightedCorner j (boundary n).ι).pt ⟶ H,
      ∃ b : W' ⊗ (Functor.const I).obj (Δ[n] : SSet.{u}) ⟶ H,
        (weightedCorner j (boundary n).ι).ι ≫ b = a) :
    TrivialKanFibration (weightedSectionsPre j H) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro t s sq
  let P := weightedCorner j (boundary n).ι
  have hw : (j ▷ (Functor.const (I)).obj (boundary n : SSet.{u})) ≫
        weightedSectionsUncurry t =
      (W ◁ (Functor.const (I)).map (boundary n).ι) ≫
        weightedSectionsUncurry s := by
    have h := congrArg weightedSectionsUncurry sq.w
    rw [weightedSectionsUncurry_comp_pre, weightedSectionsUncurry_precomp] at h
    exact h
  let a := P.isPushout.desc (weightedSectionsUncurry t) (weightedSectionsUncurry s) hw
  obtain ⟨b, hb⟩ := hcorner n a
  refine CommSq.HasLift.mk' { l := weightedSectionsLift b, fac_left := ?_, fac_right := ?_ }
  · apply (weightedSectionsHomEquiv W' H (boundary n : SSet.{u})).injective
    change weightedSectionsUncurry ((boundary n).ι ≫ weightedSectionsLift b) = _
    rw [weightedSectionsUncurry_precomp, weightedSectionsUncurry_lift]
    calc
      _ = (P.inl ≫ P.ι) ≫ b := congrArg (fun f => f ≫ b) P.inl_ι.symm
      _ = _ := by rw [Category.assoc, hb]; exact P.isPushout.inl_desc _ _ _
  · apply (weightedSectionsHomEquiv W H (Δ[n] : SSet.{u})).injective
    change weightedSectionsUncurry (weightedSectionsLift b ≫ weightedSectionsPre j H) = _
    rw [weightedSectionsUncurry_comp_pre, weightedSectionsUncurry_lift]
    calc
      _ = (P.inr ≫ P.ι) ≫ b := congrArg (fun f => f ≫ b) P.inr_ι.symm
      _ = _ := by rw [Category.assoc, hb]; exact P.isPushout.inr_desc _ _ _


/-- 射影anodyneな重み制限は、各値がKanな元の係数についてtrivial Kan fibration。 -/
theorem weightedSectionsPre_trivialKanFibration_of_projectiveHorn
    {V W H : I ⥤ SSet.{u}} (j : V ⟶ W) (hj : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.horns I).rlp.llp j)
    (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    TrivialKanFibration (weightedSectionsPre j H) := by
  apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSectionsPre_trivialKanFibration_of_corner_extensions j
  intro n a
  have hp (i : I) : Fibration ((terminal.from H).app i) := by
    letI hKan := hH i
    exact (isFibrant_iff_of_isTerminal ((terminal.from H).app i)
      (terminalIsTerminal.isTerminalObj ((CategoryTheory.evaluation I SSet.{u}).obj i) _)).mp
        inferInstance
  letI cornerLifting := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveHorn_corner_lifting I j hj (boundary n).ι (terminal.from H) hp
  let sq : CommSq a (weightedCorner j (boundary n).ι).ι
      (terminal.from H) (terminal.from _) := ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 同じ射影cofibrantな二重みに対する射影anodyne制限は、実際のホモトピー同値。 -/
theorem weightedSectionsPre_homotopyEquivalence_of_projectiveHorn
    {V W H : I ⥤ SSet.{u}} (j : V ⟶ W) (hj : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.horns I).rlp.llp j)
    (hV : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries I).rlp.llp (initial.to V))
    (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries I).rlp.llp (initial.to W))
    (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (weightedSectionsPre j H) := by
  letI sourceKan := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSections_kanComplex_of_projective_cofibrant I W hW H hH
  letI targetKan := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSections_kanComplex_of_projective_cofibrant I V hV H hH
  letI restrictionTrivial := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSectionsPre_trivialKanFibration_of_projectiveHorn j hj hH
  exact (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
