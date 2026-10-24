module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeHomLiftingEquiv
public import SerrePositivity.InfinityCategories.F1B.Fibrations.FiberwiseHomPostcomposition

/-!
概要：標的の全図式を固定する逆像上の延長と関手の族の延長の同値。
方針：curry の自然性で制限と後合成の三つの等式を両方向に移す。
規約：充填性・quasicategory 性は不要。
使われ方：相対的に組み立てた族を実際の図式へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：三つの指定を保つ図式の延長は三つの指定を保つ関手の族の延長と同値。
方針：底への射影を部分図式から回収し、標的の像の等式も curry の単射性で戻す。
規約：底上の射 i、パラメータの射 j、標的の射 U は任意。
使われ方：全空間の相対 Kan の充填を厳密な図式の延長へ変換する。 -/
lemma kanRelativeHomDiagram_lift_iff_over {C D E A A₀ : SSet.{u}}
    {K L : Over C} (i : K ⟶ L) (j : A₀ ⟶ A) (c : A ⟶ C) (U : D ⟶ E)
    (F : pullback c K.hom ⟶ D) (G : pullback (j ≫ c) L.hom ⟶ D)
    (H₀ : pullback c L.hom ⟶ E) :
    (∃ H : pullback c L.hom ⟶ D,
      overPullbackMap i (Over.mk c) ≫ H = F ∧
        (overPullbackUnderlying L.hom).map
          (Over.homMk j rfl : Over.mk (j ≫ c) ⟶ Over.mk c) ≫ H = G ∧ H ≫ U = H₀) ↔
    ∃ l : A ⟶ SerrePositivity.InfinityCategories.fiberwiseHom L.hom D,
      j ≫ l = SerrePositivity.InfinityCategories.fiberwiseHomCurry L.hom (j ≫ c) G ∧
        l ≫ SerrePositivity.InfinityCategories.fiberwiseHomPre (D := D) i = SerrePositivity.InfinityCategories.fiberwiseHomCurry K.hom c F ∧
        l ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp L.hom U = SerrePositivity.InfinityCategories.fiberwiseHomCurry L.hom c H₀ := by
  constructor
  · rintro ⟨H, hHK, hHL, hHU⟩
    refine ⟨SerrePositivity.InfinityCategories.fiberwiseHomCurry L.hom c H, ?_, ?_, ?_⟩
    · rw [← SerrePositivity.InfinityCategories.fiberwiseHomCurry_precomp, hHL]
    · erw [← kanFiberwiseHomCurry_pre i, hHK]
    · rw [← SerrePositivity.InfinityCategories.F1B.fiberwiseHomCurry_postcomp, hHU]
  · rintro ⟨l, hlj, hli, hlU⟩
    have hlp : l ≫ SerrePositivity.InfinityCategories.fiberwiseHomProjection L.hom D = c := by
      rw [← SerrePositivity.InfinityCategories.fiberwiseHomPre_projection (D := D) i, ← Category.assoc,
        hli, SerrePositivity.InfinityCategories.fiberwiseHomCurry_projection]
    let H := (SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := D) L.hom c).symm ⟨l, hlp⟩
    have hH : SerrePositivity.InfinityCategories.fiberwiseHomCurry L.hom c H = l :=
      congrArg Subtype.val ((SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := D) L.hom c).apply_symm_apply ⟨l, hlp⟩)
    refine ⟨H, ?_, ?_, ?_⟩
    · apply SerrePositivity.InfinityCategories.fiberwiseHomCurry_injective K.hom c
      erw [kanFiberwiseHomCurry_pre i c H, hH]
      exact hli
    · apply SerrePositivity.InfinityCategories.fiberwiseHomCurry_injective L.hom (j ≫ c)
      rw [SerrePositivity.InfinityCategories.fiberwiseHomCurry_precomp, hH]
      exact hlj
    · apply SerrePositivity.InfinityCategories.fiberwiseHomCurry_injective L.hom c
      calc
        SerrePositivity.InfinityCategories.fiberwiseHomCurry L.hom c (H ≫ U) =
            SerrePositivity.InfinityCategories.fiberwiseHomCurry L.hom c H ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp L.hom U :=
          SerrePositivity.InfinityCategories.F1B.fiberwiseHomCurry_postcomp L.hom U c H
        _ = l ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp L.hom U :=
          congrArg (· ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp L.hom U) hH
        _ = _ := hlU

end SerrePositivity.InfinityCategories.F1B
