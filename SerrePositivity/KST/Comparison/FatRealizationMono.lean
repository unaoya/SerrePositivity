module

public import SerrePositivity.KST.Comparison.FatNormalFormMap
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# fat realization の単射保存

概要：各行で単射である二重単体集合の射は fat realization でも単射となる。
方針：全射な標準形では添字を固定し、行の元にだけ作用することを使う。
規約：Segal 1974 Proposition 1.6、Appendix A の骨格・模型の比較の準備。
使われ方：cellular な比較と有限骨格の包含。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite

/--
概要：各行の固定次数の射が単射なら、標準形の写像も単射である。
方針：終域の単体と全射を復元してから、行の元の単射性を使う。
規約：全射性の証明は等式の判定に影響しない。
使われ方：fat realization の単射性の次数ごとの判定。
-/
theorem fatNormalFormMap_injective {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G)
    (d : SimplexCategoryᵒᵖ) (hα : ∀ n, Function.Injective ((α.app n).app d)) :
    Function.Injective (fatNormalFormMap α d) := by
  rintro ⟨k, e, he, x⟩ ⟨l, e', he', y⟩ h
  have hk : k = l := congrArg FatNormalForm.degree h
  subst l
  have hp : e = e' ∧ (α.app (op k)).app d x = (α.app (op k)).app d y := by
    simpa only [fatNormalFormMap, FatNormalForm.mk.injEq, heq_eq_eq, true_and] using h
  have hx := hα (op k) hp.2
  rcases hp.1 with rfl
  subst y
  rfl

/--
概要：各行で単射の二重単体集合の射は fat realization でも単射である。
方針：標準形との同値とその自然性で各次数の単射性へ戻す。
規約：位相的な実現やモデル構造は使わない。
使われ方：fat realization の cellular な比較。
-/
theorem fatRealizationMap_mono {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G)
    (hα : ∀ n, Mono (α.app n)) : Mono (fatRealizationMap α) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro x y h
  apply (fatNormalFormEquiv F d).injective
  change fatDegreeNormalize F d x = fatDegreeNormalize F d y
  apply fatNormalFormMap_injective α d (fun n =>
    (CategoryTheory.mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app _).mp (hα n) d))
  rw [← fatDegreeNormalize_map, ← fatDegreeNormalize_map, h]

end SerrePositivity.KST.Comparison
