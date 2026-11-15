module
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgFullLocalizationSource
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ModelRelative
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LocalizationSourceIso

/-!
概要：BE全代数の同じCAlg局所化を、一般right-frame比較のAsSmall表示へ移す。
方針：同じ全通常nerveの宇宙表示の同型と、元の弱辺の像を照合する。
規約：IS-W2 R03の既存構成の表示・局所化の移送則。置換・模型を作り直さない。
使われ方：実BE right frameと同じCAlgのnative pinched Homの比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.EInfinity.SimplicialLocalization
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable (A : Type u) [CommRing A]
local instance : ModelCategory (operad A).Algebra := modelCategory A

/-- 同じ全BE代数のAsSmall表示とHomだけを持ち上げた表示のnerveの実同型。 -/
def strictBETotModelNerveIso :
    nerve (modelRelativeCategory (operad A).Algebra).category ≅
      nerve (allAlgebraRelativeCategory A).category where
  hom := nerveMap (AsSmall.down ⋙ allAlgebraDKUp A)
  inv := nerveMap (allAlgebraDKDown A ⋙ AsSmall.up)
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro F
    apply CategoryTheory.Functor.hext
    · intro i
      rfl
    · intro i j f
      rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro F
    apply CategoryTheory.Functor.hext
    · intro i
      rfl
    · intro i j f
      rfl

/-- 同じ全BE代数の弱辺は、宇宙表示の同型で同じモデル弱辺へ移る。 -/
theorem strictBETotModelNerveIso_weakEdges :
    (strictBETotModelNerveIso A).inv.app (Opposite.op ⦋1⦌) ''
      weakNerveEdges (allAlgebraRelativeCategory A) =
        weakNerveEdges (modelRelativeCategory (operad A).Algebra) := by
  ext s
  constructor
  · rintro ⟨t, ⟨X, Y, f, hw, rfl⟩, rfl⟩
    refine ⟨_, _, (allAlgebraDKDown A ⋙ AsSmall.up).map f, ?_, ?_⟩
    · change weakEquivalences (operad A).Algebra ((allAlgebraDKDown A).map f)
      rw [modelCategory_weakEquivalences]
      exact hw
    · exact ComposableArrows.ext₁ rfl rfl (by rfl)
  · rintro ⟨X, Y, f, hf, rfl⟩
    refine ⟨ComposableArrows.mk₁ ((AsSmall.down ⋙ allAlgebraDKUp A).map f), ?_, ?_⟩
    · refine ⟨_, _, _, ?_, rfl⟩
      change weakEquivalences (operad A).Algebra (AsSmall.down.map f) at hf
      rw [modelCategory_weakEquivalences] at hf
      exact hf
    · exact ComposableArrows.ext₁ rfl rfl (by rfl)

/-- 一般right-frame比較のモデル相対圏で読んだ同じBEのCAlg源。 -/
def strictBETotModelSource :
    nerve (modelRelativeCategory (operad A).Algebra).category ⟶ CAlg_R A :=
  (strictBETotModelNerveIso A).hom ≫ allAlgebraCAlgSource A

/-- 元の同じ全局所化の普遍性は、宇宙表示を変えても保たれる。 -/
theorem strictBETotModelSource_isLocalization :
    IsLocalization (strictBETotModelSource A)
      (weakNerveEdges (modelRelativeCategory (operad A).Algebra)) := by
  apply isLocalization_of_precomposeIso (strictBETotModelNerveIso A).symm
    (strictBETotModelSource A) (weakNerveEdges (allAlgebraRelativeCategory A)) _
    (strictBETotModelNerveIso_weakEdges A)
  simpa only [strictBETotModelSource, Iso.symm_hom, Iso.inv_hom_id_assoc] using
    allAlgebraCAlgSource_isLocalization A

/-- 同じモデル相対圏表示の頂点は、元の全代数CAlg源の同じ頂点。 -/
theorem strictBETotModelSource_vertex (X : (operad A).Algebra) :
    (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (operad A).Algebra X)) =
      (algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X) := by
  change (cAlgLocalizationSource A).app (Opposite.op ⦋0⦌) _ =
    (cAlgLocalizationSource A).app (Opposite.op ⦋0⦌) _
  apply congrArg ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌))
  exact ComposableArrows.ext₀ rfl

end SerrePositivity.EInfinity.BarrattEccles
