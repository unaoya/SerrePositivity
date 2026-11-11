module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.PointJoinPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

/-!
概要：始対象を固定した、定値写像から恒等写像への収縮。
方針：coslice 射影の trivial Kan 性で恒等錐を固定した切断を選び、join の円柱を合成する。
規約：元の単体集合の quasicategory 性は不要。指定頂点の全ての定値族を固定する。
使われ方：right fibration の始点 fiber と全空間の比較。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：標準零単体から指定頂点への射は単射。
方針：各次数で始域の単体の一意性を使う。
規約：元の単体集合は任意。
使われ方：始対象下の coslice の切断で恒等錐を固定する。 -/
lemma cofinalPointInclusion_mono {B : SSet.{u}} (b : B _⦋0⦌) :
    Mono (SSet.yonedaEquiv.symm b) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro a c _
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  have ha := (a i).isLt
  have hc := (c i).isLt
  omega

/-- 概要：始対象からの恒等図式の錐は、始対象自身では恒等錐になるよう選べる。
方針：trivial Kan な coslice 射影に頂点包含を持ち上げる。
規約：切断と固定条件を厳密な射の等式で保持する。
使われ方：始対象を全時間で固定する収縮。 -/
lemma IsInitialVertex.exists_fixed_coslice_section {B : SSet.{u}} {b : B _⦋0⦌}
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex b) :
    ∃ s : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm b),
      s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b) = 𝟙 B ∧
      SSet.yonedaEquiv.symm b ≫ s = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone b) := by
  have := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration b).mp hb
  have := cofinalPointInclusion_mono b
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b))
    (SSet.yonedaEquiv.symm b) inferInstance
  have hs : CommSq (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone b)) (SSet.yonedaEquiv.symm b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b)) (𝟙 B) := by
    constructor
    rw [SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_projection, Category.comp_id]
  exact ⟨hs.lift, hs.fac_right, hs.fac_left⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex export _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsInitialVertex (exists_fixed_coslice_section)


/-- 概要：始対象を固定する定値写像から恒等写像への prism が存在する。
方針：固定した coslice の切断を uncurry し、点と図式の join の円柱を合成する。
規約：全てのパラメータで始対象への定値図式を固定する。
使われ方：right fibration の始点 fiber の比較と Quillen A の十分性。 -/
lemma IsInitialVertex.exists_fixed_initial_prism {B : SSet.{u}} {b : B _⦋0⦌}
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex b) :
    ∃ C : (Δ[1] : SSet.{u}) ⊗ B ⟶ B,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ C = SSet.const b ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ C = 𝟙 B ∧
      ∀ K : SSet.{u}, (Δ[1] ◁ (SSet.const b : K ⟶ B)) ≫ C = SSet.const b := by
  obtain ⟨s, hsp, hsb⟩ := hb.exists_fixed_coslice_section
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry s
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (SSet.yonedaEquiv.symm b) ≫ F = SSet.const b := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, hsb, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
    rfl
  let C := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.cofinalPointJoinPrism B ≫ F
  refine ⟨C, ?_, ?_, ?_⟩
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.cofinalPointJoinPrism B ≫ F = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.cofinalPointJoinPrism_zero, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed,
      SSet.yonedaEquiv_symm_zero, SSet.comp_const]
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.cofinalPointJoinPrism B ≫ F = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.cofinalPointJoinPrism_one, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection, hsp]
  · intro K
    change (Δ[1] ◁ (SSet.const b : K ⟶ B)) ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.cofinalPointJoinPrism B ≫ F = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.cofinalPointJoinPrism_naturality, Category.assoc]
    have hfact : (SSet.const b : K ⟶ B) =
        SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ≫ SSet.yonedaEquiv.symm b := by
      rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const]
    have hmap : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (SSet.const b : K ⟶ B) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u}))
          (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0]) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (SSet.yonedaEquiv.symm b) := by
      rw [hfact]
      simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (𝟙 (Δ[0] : SSet.{u})) (𝟙 _)
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0]) (SSet.yonedaEquiv.symm b)
    rw [hmap]
    simp only [Category.assoc, hF, SSet.comp_const]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex export _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsInitialVertex (exists_fixed_initial_prism)


end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
