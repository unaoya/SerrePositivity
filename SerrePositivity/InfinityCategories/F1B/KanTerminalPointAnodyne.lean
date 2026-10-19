module

public import SerrePositivity.InfinityCategories.F1B.KanRightPointJoinPrism
public import SerrePositivity.InfinityCategories.F1B.InitialFixedContraction
public import SerrePositivity.InfinityCategories.F1B.TerminalHomotopyAnodyne
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-!
概要：指定終対象への一点の包含は right anodyne。
方針：恒等錐を固定する slice の切断から終対象を固定する収縮を作る。
規約：周囲の quasicategory 性は不要で、終対象の境界充填条件だけを使う。
使われ方：像の点で左 Kan の局所余錐を一点へ制限する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：終対象への恒等図式の錐を、終対象自身で恒等錐になるよう選べる。
方針：自明 Kan な slice 射影に一点の包含を持ち上げる。
規約：切断と固定条件を厳密な等式で保持する。
使われ方：指定終対象を固定する収縮の構成。 -/
lemma kanExists_fixed_slice_section {B : SSet.{u}} {b : B _⦋0⦌}
    (hb : IsTerminalVertex b) :
    ∃ s : B ⟶ sliceOver (SSet.yonedaEquiv.symm b),
      s ≫ sliceOverProjection (SSet.yonedaEquiv.symm b) = 𝟙 B ∧
      SSet.yonedaEquiv.symm b ≫ s = SSet.yonedaEquiv.symm (sliceIdentityCone b) := by
  have := (isTerminalVertex_iff_trivialKanFibration b).mp hb
  have := cofinalPointInclusion_mono b
  have := TrivialKanFibration.mem (p := sliceOverProjection (SSet.yonedaEquiv.symm b))
    (SSet.yonedaEquiv.symm b) inferInstance
  have hs : CommSq (SSet.yonedaEquiv.symm (sliceIdentityCone b)) (SSet.yonedaEquiv.symm b)
      (sliceOverProjection (SSet.yonedaEquiv.symm b)) (𝟙 B) := by
    constructor
    rw [SSet.yonedaEquiv_symm_comp, sliceIdentityCone_projection, Category.comp_id]
  exact ⟨hs.lift, hs.fac_right, hs.fac_left⟩

/-- 概要：終対象を固定する恒等写像から定値写像への prism が存在する。
方針：固定した slice の切断を展開し、右点 join の prism を合成する。
規約：指定終対象への全ての定値パラメータ族を固定する。
使われ方：終対象の一点包含の right anodyne 性。 -/
lemma kanExists_fixed_terminal_prism {B : SSet.{u}} {b : B _⦋0⦌}
    (hb : IsTerminalVertex b) :
    ∃ C : (Δ[1] : SSet.{u}) ⊗ B ⟶ B,
      prismEndpoint 0 B ≫ C = 𝟙 B ∧ prismEndpoint 1 B ≫ C = SSet.const b ∧
      ∀ K : SSet.{u}, (Δ[1] ◁ (SSet.const b : K ⟶ B)) ≫ C = SSet.const b := by
  obtain ⟨s, hsp, hsb⟩ := kanExists_fixed_slice_section hb
  let F := sliceOverUncurry s
  have hF : joinMap (SSet.yonedaEquiv.symm b) (𝟙 (Δ[0] : SSet.{u})) ≫ F =
      SSet.const b := by
    rw [← sliceOverUncurry_precomp, hsb, sliceOverUncurry_yoneda]
    rfl
  let C := kanRightPointJoinPrism B ≫ F
  refine ⟨C, ?_, ?_, ?_⟩
  · change prismEndpoint 0 B ≫ kanRightPointJoinPrism B ≫ F = _
    rw [← Category.assoc, kanRightPointJoinPrism_zero, sliceOverUncurry_projection, hsp]
  · change prismEndpoint 1 B ≫ kanRightPointJoinPrism B ≫ F = _
    rw [← Category.assoc, kanRightPointJoinPrism_one, Category.assoc,
      sliceOverUncurry_fixed, SSet.yonedaEquiv_symm_zero, SSet.comp_const]
  · intro K
    change (Δ[1] ◁ (SSet.const b : K ⟶ B)) ≫ kanRightPointJoinPrism B ≫ F = _
    rw [← Category.assoc, kanRightPointJoinPrism_naturality, Category.assoc]
    have hfact : (SSet.const b : K ⟶ B) =
        SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ≫ SSet.yonedaEquiv.symm b := by
      rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const]
    have hmap : joinMap (SSet.const b : K ⟶ B) (𝟙 (Δ[0] : SSet.{u})) =
        joinMap (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0]) (𝟙 Δ[0]) ≫
          joinMap (SSet.yonedaEquiv.symm b) (𝟙 (Δ[0] : SSet.{u})) := by
      rw [hfact]
      simpa only [Category.id_comp] using joinMap_comp
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0])
        (SSet.yonedaEquiv.symm b) (𝟙 (Δ[0] : SSet.{u})) (𝟙 (Δ[0] : SSet.{u}))
    rw [hmap]
    simp only [Category.assoc, hF, SSet.comp_const]

/-- 概要：終対象を選ぶ一点の包含は right anodyne。
方針：終対象を固定する収縮を、終点ホーンの pushout-product の retract として使う。
規約：単体集合 B に quasicategory 性を要求しない。
使われ方：局所余錐の余極限性を終対象の脚で判定する。 -/
lemma kanTerminalPoint_rightAnodyne {B : SSet.{u}} {b : B _⦋0⦌}
    (hb : IsTerminalVertex b) : rightAnodyneExtensions (SSet.yonedaEquiv.symm b) := by
  have := cofinalPointInclusion_mono b
  obtain ⟨C, h₀, h₁, hfix⟩ := kanExists_fixed_terminal_prism hb
  let r := stdSimplex.isTerminalObj₀.from B
  apply rightAnodyneExtensions_of_fixed_terminal_homotopy (SSet.yonedaEquiv.symm b) r
    (stdSimplex.isTerminalObj₀.hom_ext _ _) C h₀
  · simpa only [SSet.yonedaEquiv_symm_zero, SSet.comp_const] using h₁
  · simpa only [SSet.yonedaEquiv_symm_zero, SSet.comp_const] using hfix (Δ[0] : SSet.{u})

end SerrePositivity.InfinityCategories.F1B
