module
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgFullLocalizationSource
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ModelRelative
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LocalizationSourceIso

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：BE全代数の同じCAlg局所化を、一般right-frame比較のAsSmall表示へ移す。
方針：同じ全通常nerveの宇宙表示の同型と、元の弱辺の像を照合する。
規約：IS-W2 R03の既存構成の表示・局所化の移送則。置換・模型を作り直さない。
使われ方：実BE right frameと同じCAlgのnative pinched Homの比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]
local instance _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.instModelCategoryAlgebraOperad : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A

/-- 同じ全BE代数のAsSmall表示とHomだけを持ち上げた表示のnerveの実同型。 -/
def strictBETotModelNerveIso :
    nerve (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).category ≅
      nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.allAlgebraRelativeCategory A).category where
  hom := nerveMap (AsSmall.down ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.allAlgebraDKUp A)
  inv := nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.allAlgebraDKDown A ⋙ AsSmall.up)
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
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelNerveIso A).inv.app (Opposite.op ⦋1⦌) ''
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.EInfinity.BarrattEccles.allAlgebraRelativeCategory A) =
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := by
  ext s
  constructor
  · rintro ⟨t, ⟨X, Y, f, hw, rfl⟩, rfl⟩
    refine ⟨_, _, (_root_.SerrePositivity.EInfinity.BarrattEccles.allAlgebraDKDown A ⋙ AsSmall.up).map f, ?_, ?_⟩
    · change weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ((_root_.SerrePositivity.EInfinity.BarrattEccles.allAlgebraDKDown A).map f)
      rw [_root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory_weakEquivalences]
      exact hw
    · exact ComposableArrows.ext₁ rfl rfl (by rfl)
  · rintro ⟨X, Y, f, hf, rfl⟩
    refine ⟨ComposableArrows.mk₁ ((AsSmall.down ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.allAlgebraDKUp A).map f), ?_, ?_⟩
    · refine ⟨_, _, _, ?_, rfl⟩
      change weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra (AsSmall.down.map f) at hf
      rw [_root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory_weakEquivalences] at hf
      exact hf
    · exact ComposableArrows.ext₁ rfl rfl (by rfl)

/-- 一般right-frame比較のモデル相対圏で読んだ同じBEのCAlg源。 -/
def strictBETotModelSource :
    nerve (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).category ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelNerveIso A).hom ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.allAlgebraCAlgSource A

/-- 元の同じ全局所化の普遍性は、宇宙表示を変えても保たれる。 -/
theorem strictBETotModelSource_isLocalization :
    IsLocalization (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)) := by
  apply isLocalization_of_precomposeIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelNerveIso A).symm
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.EInfinity.BarrattEccles.allAlgebraRelativeCategory A)) _
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelNerveIso_weakEdges A)
  simpa only [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource, Iso.symm_hom, Iso.inv_hom_id_assoc] using
    _root_.SerrePositivity.EInfinity.BarrattEccles.allAlgebraCAlgSource_isLocalization A

/-- 同じモデル相対圏表示の頂点は、元の全代数CAlg源の同じ頂点。 -/
theorem strictBETotModelSource_vertex (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra X)) =
      (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X) := by
  change (_root_.SerrePositivity.EInfinity.BarrattEccles.cAlgLocalizationSource A).app (Opposite.op ⦋0⦌) _ =
    (_root_.SerrePositivity.EInfinity.BarrattEccles.cAlgLocalizationSource A).app (Opposite.op ⦋0⦌) _
  apply congrArg ((_root_.SerrePositivity.EInfinity.BarrattEccles.cAlgLocalizationSource A).app (Opposite.op ⦋0⦌))
  exact ComposableArrows.ext₀ rfl

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
