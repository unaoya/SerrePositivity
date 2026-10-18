module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedSectionOverEvaluation

/-!
概要：weighted nerve の切断の族を Bousfield–Kan 重みの自然変換へ戻す。
方針：over 圏の射列の終点での評価を全次数と全添字で束ねる。
規約：底の射影を保つ条件を明示し、Kan 性は要求しない。
使われ方：Kerodon 5.3.3.1、7.5.3.12 の重み付き end と切断空間の逆対応。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {I : Type u} [SmallCategory I] {A : SSet.{u}} {H : I ⥤ SSet.{u}}

/-- 概要：切断の族の終点での評価は、各 over 圏の nerve とパラメータからの単体的射になる。
方針：標準単体からの評価を Yoneda で単体に戻し、制限の公式を使う。
規約：i は元の小さい圏の任意の対象。
使われ方：Kerodon 5.3.3.1、7.5.3.12 の逆対応の各成分。 -/
noncomputable def weightedSectionOverMap (s : nerve I ⊗ A ⟶ weightedNerve H)
    (hs : s ≫ weightedNerveProjection H = fst (nerve I) A) (i : I) :
    nerve (Over i) ⊗ A ⟶ H.obj i where
  app d := ↾fun t => SSet.yonedaEquiv (weightedSectionOverSimplex s hs t.1 t.2)
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, a⟩
    change SSet.yonedaEquiv (weightedSectionOverSimplex s hs
      ((SimplexCategory.toCat.map α.unop).toFunctor ⋙ σ) (A.map α a)) =
        (H.obj i).map α (SSet.yonedaEquiv (weightedSectionOverSimplex s hs σ a))
    apply SSet.yonedaEquiv.symm.injective
    rw [Equiv.symm_apply_apply]
    have hy := (SSet.yonedaEquiv_symm_naturality_left (X := H.obj i) α.unop
      (SSet.yonedaEquiv (weightedSectionOverSimplex s hs σ a))).symm
    rw [Equiv.symm_apply_apply] at hy
    exact (weightedSectionOverSimplex_restriction s hs α.unop σ a).trans hy.symm

/-- 概要：切断の族の over 圏での評価は終点の後合成と自然である。
方針：全次数で終点を移す評価の公式を使う。
規約：重みとパラメータの直積のうち重みの因子だけを後合成する。
使われ方：Kerodon 5.3.3.1、7.5.3.12 の Bousfield–Kan 重みの自然性。 -/
lemma weightedSectionOverMap_naturality (s : nerve I ⊗ A ⟶ weightedNerve H)
    (hs : s ≫ weightedNerveProjection H = fst (nerve I) A) {i j : I} (f : i ⟶ j) :
    ((bousfieldKanWeight I).map f ⊗ₘ 𝟙 A) ≫ weightedSectionOverMap s hs j =
      weightedSectionOverMap s hs i ≫ H.map f := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, a⟩
  change SSet.yonedaEquiv (weightedSectionOverSimplex s hs (σ ⋙ Over.map f) a) =
    (H.map f).app (Opposite.op ⦋n⦌) (SSet.yonedaEquiv (weightedSectionOverSimplex s hs σ a))
  rw [weightedSectionOverSimplex_map, SSet.yonedaEquiv_comp]

/-- 概要：weighted nerve の切断の族から Bousfield–Kan 重みの自然変換を得る。
方針：各 over 圏の射列での評価とその終点に関する自然性を組み合わせる。
規約：逆関係は後続の検証であり、この定義は自然変換の構成までを含む。
使われ方：Kerodon 5.3.3.1、7.5.3.12 の切断から重み付き end への比較。 -/
noncomputable def weightedSectionTransform (s : nerve I ⊗ A ⟶ weightedNerve H)
    (hs : s ≫ weightedNerveProjection H = fst (nerve I) A) :
    bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H where
  app i := weightedSectionOverMap s hs i
  naturality _ _ f := weightedSectionOverMap_naturality s hs f

end SerrePositivity.InfinityCategories.HomotopyLimits
