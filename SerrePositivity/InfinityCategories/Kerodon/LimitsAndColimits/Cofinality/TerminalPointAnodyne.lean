module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightPointJoinPrism
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialFixedContraction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TerminalHomotopyAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-!
概要：指定終対象への一点の包含は right anodyne。
方針：恒等錐を固定する slice の切断から終対象を固定する収縮を作る。
規約：周囲の quasicategory 性は不要で、終対象の境界充填条件だけを使う。
使われ方：像の点で左 Kan の局所余錐を一点へ制限する。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：終対象への恒等図式の錐を、終対象自身で恒等錐になるよう選べる。
方針：自明 Kan な slice 射影に一点の包含を持ち上げる。
規約：切断と固定条件を厳密な等式で保持する。
使われ方：指定終対象を固定する収縮の構成。 -/
lemma exists_fixed_slice_section {B : SSet.{u}} {b : B _⦋0⦌}
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex b) :
    ∃ s : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm b),
      s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b) = 𝟙 B ∧
      SSet.yonedaEquiv.symm b ≫ s = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone b) := by
  have := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration b).mp hb
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointInclusion_mono b
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b))
    (SSet.yonedaEquiv.symm b) inferInstance
  have hs : CommSq (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone b)) (SSet.yonedaEquiv.symm b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b)) (𝟙 B) := by
    constructor
    rw [SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone_projection, Category.comp_id]
  exact ⟨hs.lift, hs.fac_right, hs.fac_left⟩

/-- 概要：終対象を固定する恒等写像から定値写像への prism が存在する。
方針：固定した slice の切断を展開し、右点 join の prism を合成する。
規約：指定終対象への全ての定値パラメータ族を固定する。
使われ方：終対象の一点包含の right anodyne 性。 -/
lemma exists_fixed_terminal_prism {B : SSet.{u}} {b : B _⦋0⦌}
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex b) :
    ∃ C : (Δ[1] : SSet.{u}) ⊗ B ⟶ B,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ C = 𝟙 B ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ C = SSet.const b ∧
      ∀ K : SSet.{u}, (Δ[1] ◁ (SSet.const b : K ⟶ B)) ≫ C = SSet.const b := by
  obtain ⟨s, hsp, hsb⟩ := exists_fixed_slice_section hb
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry s
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm b) (𝟙 (Δ[0] : SSet.{u})) ≫ F =
      SSet.const b := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, hsb, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda]
    rfl
  let C := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightPointJoinPrism B ≫ F
  refine ⟨C, ?_, ?_, ?_⟩
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightPointJoinPrism B ≫ F = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightPointJoinPrism_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, hsp]
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightPointJoinPrism B ≫ F = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightPointJoinPrism_one, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed, SSet.yonedaEquiv_symm_zero, SSet.comp_const]
  · intro K
    change (Δ[1] ◁ (SSet.const b : K ⟶ B)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightPointJoinPrism B ≫ F = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightPointJoinPrism_naturality, Category.assoc]
    have hfact : (SSet.const b : K ⟶ B) =
        SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ≫ SSet.yonedaEquiv.symm b := by
      rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const]
    have hmap : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.const b : K ⟶ B) (𝟙 (Δ[0] : SSet.{u})) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0]) (𝟙 Δ[0]) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm b) (𝟙 (Δ[0] : SSet.{u})) := by
      rw [hfact]
      simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0])
        (SSet.yonedaEquiv.symm b) (𝟙 (Δ[0] : SSet.{u})) (𝟙 (Δ[0] : SSet.{u}))
    rw [hmap]
    simp only [Category.assoc, hF, SSet.comp_const]

/-- 概要：終対象を選ぶ一点の包含は right anodyne。
方針：終対象を固定する収縮を、終点ホーンの pushout-product の retract として使う。
規約：単体集合 B に quasicategory 性を要求しない。
使われ方：局所余錐の余極限性を終対象の脚で判定する。 -/
lemma terminalPoint_rightAnodyne {B : SSet.{u}} {b : B _⦋0⦌}
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex b) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (SSet.yonedaEquiv.symm b) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointInclusion_mono b
  obtain ⟨C, h₀, h₁, hfix⟩ := exists_fixed_terminal_prism hb
  let r := stdSimplex.isTerminalObj₀.from B
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.rightAnodyneExtensions_of_fixed_terminal_homotopy (SSet.yonedaEquiv.symm b) r
    (stdSimplex.isTerminalObj₀.hom_ext _ _) C h₀
  · simpa only [SSet.yonedaEquiv_symm_zero, SSet.comp_const] using h₁
  · simpa only [SSet.yonedaEquiv_symm_zero, SSet.comp_const] using hfix (Δ[0] : SSet.{u})

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.4.4.5" (partial := direction) "仮定：右ファイブレーションの全空間の指定頂点が終対象（HTT の (2) と一致）。結論：指定点の包含に沿う制限は、任意の右ファイブレーションへの底上の関手空間で自明 Kan ファイブレーションになり、反変同値になる（(2)⇒(3) が一致。他の向きと指定 η による判定は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.terminalPoint_rightAnodyne
