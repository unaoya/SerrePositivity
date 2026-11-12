module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.BridgeStageKernel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PairValueRepresentatives

/-!
概要：D の段階同一視と有限検出から、比較射の正次数の全基点単射性を導く。
方針：二球面を一度だけ検出し、同じ path の両端で像の等式を比較する。
規約：D の構造を直接消費し、二代表の基点経路を共有する。
使われ方：元の余錐比較の Whitehead 判定の単射性。
-/

@[expose] public section
noncomputable section
universe u w
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
open KST.Spectra

/-- 元の脚と段階にホモトピーまで可換な比較は、D の等式検出から全基点で単射。 -/
lemma bridge_positive_injective {I : Type u} [PartialOrder I]
    (X : I → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w}) (A T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w})
    (τ : ∀ {i j : I}, i ≤ j → ((X i).obj ⟶ (X j).obj))
    (l : ∀ i : I, (X i).obj ⟶ A.obj)
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactSpacePiData X A τ l)
    (s : ∀ i : I, (X i).obj ⟶ T.obj) (q : T.obj ⟶ A.obj)
    (hcomm : ∀ i : I, Nonempty (Homotopy (l i) (s i ≫ q)))
    (hstage : ∀ (i j : I) (hij : i ≤ j), Nonempty (Homotopy (s i) (τ hij ≫ s j)))
    (hfinite : ∀ {K : SSet.{w}} [K.Finite] (f : K ⟶ T.obj),
      ∃ i : I, ∃ g : K ⟶ (X i).obj, Nonempty (Homotopy f (g ≫ s i)))
    (n : ℕ) (x : T.obj _⦋0⦌) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) q (x := x) rfl) := by
  intro a b hab
  obtain ⟨i, y, β, z, h₀, h₁, γ, hγ⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.finite_positive_pair_representative X T.obj s hfinite n x ![a, b]
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map q rfl
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation T.obj 0) h₀ (γ 0)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map q rfl
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation T.obj 0) h₀ (γ 1)) := by
    simpa only [(hγ 0).1, (hγ 1).1, Matrix.cons_val_zero, Matrix.cons_val_one] using hab
  have hr := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.shared_path_map_equality_iff q n z h₀ h₁ (γ 0) (γ 1)).mp hl
  rw [(hγ 0).2, (hγ 1).2] at hr
  obtain ⟨H⟩ := hcomm i
  have hm (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X i).obj n y) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (s i ≫ q) rfl c =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map q rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (s i) rfl c) :=
    DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (s i) rfl q rfl rfl) c
  have he : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (l i) y (β 0) = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (l i) y (β 1) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.homotopy_map_equality_iff H n y (β 0) (β 1)).mpr
      ((hm (β 0)).trans (hr.trans (hm (β 1)).symm))
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.bridge_stage_positive_kernel X A T τ l h s hstage n i y (β 0) (β 1) he
  have hγeq : γ 0 = γ 1 :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_bijective_of_piIsomorphism n (KanPath.evaluation T.obj 1)
      (KanPath.evaluation_piIsomorphism T.obj 1) h₁).injective
        ((hγ 0).2.trans (hs.trans (hγ 1).2.symm))
  have ha := (hγ 0).1
  have hb := (hγ 1).1
  exact ha.symm.trans ((congrArg
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation T.obj 0) h₀) hγeq).trans hb)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
