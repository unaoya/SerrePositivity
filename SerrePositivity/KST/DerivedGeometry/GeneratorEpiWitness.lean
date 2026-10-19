module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
概要：全射の終域の真部分対象を経由しない生成対象からの射を構成する。
方針：pullback の単射へ生成対象の検出性を適用し、全射性で真部分対象との矛盾を得る。
規約：生成対象は projective と仮定しない。
使われ方：Stacks Lemma 19.12.1 (079J)・19.12.2、TT §3・§8、Toën §3.2 の小さい試験集合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u
open CategoryTheory Limits Opposite
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/--
概要：全射の終域の真部分対象を経由しない生成対象からの合成が存在する。
方針：全ての合成が部分対象を経由するなら、その pullback が生成対象で検出される同型となる。
規約：全射に対する生成対象からの射の持ち上げは仮定しない。
使われ方：Stacks 19.12.1、TT §3 の小さい全射部分対象の存在。
-/
lemma exists_generator_map_not_factor (G : C) (hG : IsSeparator G)
    {M N : C} (p : M ⟶ N) [Epi p] (S : Subobject N) (hS : S ≠ ⊤) :
    ∃ f : G ⟶ M, ¬ ∃ g : G ⟶ (S : C), g ≫ S.arrow = f ≫ p := by
  classical
  by_contra! hf
  let j := pullback.fst p S.arrow
  have hj : IsIso j := by
    apply (hG.isDetector.isIso_iff_of_mono j).mpr
    intro X hX f
    simp only [ObjectProperty.singleton_iff] at hX
    subst X
    obtain ⟨g, hg⟩ := hf f
    exact ⟨pullback.lift f g hg.symm, by simp [j]⟩
  have he : (inv j ≫ pullback.snd p S.arrow) ≫ S.arrow = p := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    change (inv j ≫ j) ≫ p = p
    simp
  have : Epi S.arrow := epi_of_epi_fac he
  have : IsIso S.arrow := isIso_of_mono_of_epi _
  exact hS (Subobject.eq_top_of_isIso_arrow S)

end SerrePositivity.KST.DerivedGeometry
