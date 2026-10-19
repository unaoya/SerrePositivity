module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinInvertingRestriction

/-!
概要：関手の族の制限の持ち上げと、二つの部分図式を保つ実際の図式の延長を同定する。
方針：相対指数の普遍性と前合成の自然性を両方向に適用する。
規約：充填性や quasicategory 性は不要。
使われ方：族の相対骨格上の延長を相対 join 上の図式へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：二つの部分図式を固定した延長は、族の制限の持ち上げと同値。
方針：curry の自然性で順方向を示し、底への射影を復元して逆方向を uncurry する。
規約：底上の射 i とパラメータの射 j は任意。
使われ方：相対 join の族の延長を実際の図式の延長へ移す。 -/
lemma kanRelativeHomDiagram_lift_iff {C D A A₀ : SSet.{u}}
    {K L : Over C} (i : K ⟶ L) (j : A₀ ⟶ A) (c : A ⟶ C)
    (F : pullback c K.hom ⟶ D) (G : pullback (j ≫ c) L.hom ⟶ D) :
    (∃ H : pullback c L.hom ⟶ D,
      overPullbackMap i (Over.mk c) ≫ H = F ∧
        (overPullbackUnderlying L.hom).map
          (Over.homMk j rfl : Over.mk (j ≫ c) ⟶ Over.mk c) ≫ H = G) ↔
    ∃ l : A ⟶ kanFiberwiseHom L.hom D,
      j ≫ l = kanFiberwiseHomCurry L.hom (j ≫ c) G ∧
        l ≫ kanFiberwiseHomPre (D := D) i = kanFiberwiseHomCurry K.hom c F := by
  constructor
  · rintro ⟨H, hHK, hHL⟩
    refine ⟨kanFiberwiseHomCurry L.hom c H, ?_, ?_⟩
    · rw [← kanFiberwiseHomCurry_precomp]
      rw [hHL]
    · erw [← kanFiberwiseHomCurry_pre i, hHK]
  · rintro ⟨l, hlj, hli⟩
    have hlp : l ≫ kanFiberwiseHomProjection L.hom D = c := by
      rw [← kanFiberwiseHomPre_projection (D := D) i, ← Category.assoc,
        hli, kanFiberwiseHomCurry_projection]
    let H := (kanFiberwiseHomEquiv (D := D) L.hom c).symm ⟨l, hlp⟩
    have hH : kanFiberwiseHomCurry L.hom c H = l :=
      congrArg Subtype.val ((kanFiberwiseHomEquiv (D := D) L.hom c).apply_symm_apply ⟨l, hlp⟩)
    refine ⟨H, ?_, ?_⟩
    · apply kanFiberwiseHomCurry_injective K.hom c
      erw [kanFiberwiseHomCurry_pre i, hH]
      exact hli
    · apply kanFiberwiseHomCurry_injective L.hom (j ≫ c)
      erw [kanFiberwiseHomCurry_precomp, hH]
      exact hlj

end SerrePositivity.InfinityCategories.F1B
