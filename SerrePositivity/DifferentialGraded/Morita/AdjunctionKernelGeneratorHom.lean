module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelTelescope

/-! # 一般kernel右随伴の生成元上のHom比較

## 概要
構成したtelescopeからの標的射が、全てのshiftした代表加群でHom全単射を与える。

## 方針
全射性は初期被覆、単射性はcompact性による有限段階因子分解と直後の関係消去から示す。

## 規約と注意
任意可換環と独立対象宇宙で成立し、局所Hom K-flat性・kernel列の射影性を仮定しない。

## 使われ方
U16aの全入力でのHom表現可能性を局所化帰納で示す際の生成元の基底。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)
  (Y : DerivedModuleCategory A E) (S : KernelBrownTelescope A D E K Y)

/-- 生成元の像からYへの任意射は、telescopeの像を経由する。 -/
lemma kernelBrownTelescope_generator_surjective (p : D × ℤ)
    (f : (kernelDerivedTensor A D E K).obj (moduleCompactGenerators A D p) ⟶ Y) :
    ∃ g : moduleCompactGenerators A D p ⟶ S.obj,
      (kernelDerivedTensor A D E K).map g ≫ S.target = f := by
  obtain ⟨g, hg⟩ := kernelBrownApproximation_generator_surjective A D E K Y 0 p f
  refine ⟨g ≫ kernelBrownStageMap A D E K Y S 0, ?_⟩
  rw [Functor.map_comp, Category.assoc, kernelBrownStageMap_fac, hg]

/-- 生成元からtelescopeへの射が標的で零なら、それ自体が零。 -/
lemma kernelBrownTelescope_generator_kernel_zero (p : D × ℤ)
    (f : moduleCompactGenerators A D p ⟶ S.obj)
    (hf : (kernelDerivedTensor A D E K).map f ≫ S.target = 0) : f = 0 := by
  obtain ⟨n, g, hg⟩ := moduleCompact_telescope_factor A D
    (kernelBrownObjects A D E K Y) (kernelBrownTransition A D E K Y)
    (moduleCompactGenerators_compact A D p) S.inclusion S.boundary S.distinguished f
  change f = g ≫ kernelBrownStageMap A D E K Y S n at hg
  have hz : (kernelDerivedTensor A D E K).map g ≫
      (kernelBrownApproximation A D E K Y n).target = 0 := by
    rw [hg, Functor.map_comp, Category.assoc, kernelBrownStageMap_fac] at hf
    exact hf
  rw [hg, ← kernelBrownStageMap_succ A D E K Y S n, ← Category.assoc,
    kernelBrownTransition_kills A D E K Y n p g hz, zero_comp]

/-- telescopeの標的射は全てのcompact生成元でHomの全単射を与える。 -/
lemma kernelBrownTelescope_generator_bijective (p : D × ℤ) :
    Function.Bijective (fun f : moduleCompactGenerators A D p ⟶ S.obj =>
      (kernelDerivedTensor A D E K).map f ≫ S.target) := by
  let L := kernelDerivedTensor A D E K
  let : L.Additive := kernelBrownActionAdditive A D E K
  constructor
  · intro f g h
    change L.map f ≫ S.target = L.map g ≫ S.target at h
    apply sub_eq_zero.mp
    apply kernelBrownTelescope_generator_kernel_zero A D E K Y S p (f-g)
    change L.map (f-g) ≫ S.target = 0
    rw [L.map_sub, sub_comp, h, sub_self]
  · exact kernelBrownTelescope_generator_surjective A D E K Y S p

end SerrePositivity.DifferentialGraded.Morita
