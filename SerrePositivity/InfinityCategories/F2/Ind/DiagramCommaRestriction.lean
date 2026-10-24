module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaEvaluation
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PreFiberKan

/-!
概要：元の図式 comma の形状制限と、元の全余錐・各点評価の自然性。
方針：全図式 Yoneda の厳密な自然性から同じ comma の作用を作る。
規約：形状には有限性を課さず、元の図式と全変換を保持する。
使われ方：有限半順序形状の点追加で旧図式と下方図式を照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {J K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C) (f : J ⟶ K)
/-- 概要：元の全図式 comma を同じ形状包含で制限する。
方針：同じ comma の作用を使う。規約：全射の等号。使われ方：点追加の境界回収。 -/
def diagramCommaRestriction : diagramComma κ D ⟶
    diagramComma κ ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D) :=
  commaPostcomp (diagramYoneda κ K C) (diagramYoneda κ J C)
    ((SSet.uliftFunctor.{u + 1, u}).map ((pre f).app C))
    ((pre ((SSet.uliftFunctor.{u + 1, u}).map f)).app (IndInfinity κ C))
    (diagramYoneda_restrict κ f) (functorVertex D)
/-- 概要：制限は元の C 側の全図式を厳密に保つ。
方針：同じ comma の作用を使う。規約：全射の等号。使われ方：点追加の境界回収。 -/
lemma diagramCommaRestriction_projection : diagramCommaRestriction κ D f ≫
    diagramCommaProjection κ ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D) =
      diagramCommaProjection κ D ≫ (SSet.uliftFunctor.{u + 1, u}).map ((pre f).app C) :=
  commaPostcomp_projection _ _ _ _ _ _
/-- 概要：任意の全族の全錐は元の全錐の制限そのもの。
方針：同じ comma の作用を使う。規約：全射の等号。使われ方：点追加の境界回収。 -/
lemma diagramCommaRestriction_uncurry {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D) :
    sliceOverUncurry (q ≫ diagramCommaRestriction κ D f ≫
      pullback.snd (diagramYoneda κ J C) (sliceOverProjection (SSet.yonedaEquiv.symm
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D))))) =
    sliceOverUncurry (q ≫ pullback.snd (diagramYoneda κ K C)
      (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex D)))) ≫
        ((pre ((SSet.uliftFunctor.{u + 1, u}).map f)).app (IndInfinity κ C)) :=
  commaPostcomp_uncurry _ _ _ _ _ _ q
/-- 概要：同じ標準全余錐の制限を厳密に回収する。
方針：同じ comma の作用を使う。規約：全射の等号。使われ方：点追加の境界回収。 -/
lemma diagramCommaRestriction_coconeMap :
    joinMap (diagramCommaRestriction κ D f) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      (diagramCommaCocone κ ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D)).val =
    (diagramCommaCocone κ D).val ≫
      ((pre ((SSet.uliftFunctor.{u + 1, u}).map f)).app (IndInfinity κ C)) := by
  change joinMap _ (𝟙 Δ[0]) ≫ sliceOverUncurry _ = _
  rw [← sliceOverUncurry_precomp]
  simpa only [Category.id_comp, diagramCommaCocone] using
    diagramCommaRestriction_uncurry κ D f (𝟙 _)
/-- 概要：形状制限と元の頂点での評価は厳密に可換。
方針：同じ comma の作用を使う。規約：全射の等号。使われ方：点追加の境界回収。 -/
lemma diagramCommaRestriction_evaluate (j : J _⦋0⦌) :
    diagramCommaRestriction κ D f ≫
      diagramCommaEvaluation κ ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D) j =
    diagramCommaEvaluation κ D (f.app (Opposite.op ⦋0⦌) j) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, diagramCommaEvaluation_projection]
    rw [← Category.assoc, diagramCommaRestriction_projection, Category.assoc,
      ← Functor.map_comp, evaluateFunctorAt_pre]
    have h := (diagramCommaEvaluation_projection κ D (f.app (Opposite.op ⦋0⦌) j)).symm
    convert h using 1
    rfl
  · apply sliceOverUncurry_injective
    have hr := diagramCommaRestriction_uncurry κ D f (𝟙 _)
    have he := diagramCommaEvaluation_uncurry κ D (f.app (Opposite.op ⦋0⦌) j) (𝟙 _)
    simp only [Category.id_comp] at hr he
    have hl := diagramCommaEvaluation_uncurry κ
      ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D) j (diagramCommaRestriction κ D f)
    rw [hr, Category.assoc, evaluateFunctorAt_pre] at hl
    have hx := hl.trans he.symm
    convert hx using 1 <;> rfl

end SerrePositivity.InfinityCategories.F2.Ind
