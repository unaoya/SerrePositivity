module

public import SerrePositivity.InfinityCategories.F1.CoherentTwoSidedHomLeftModel

/-!
概要：補間段階の左端を、元の左 Hom 比較の区間族そのものへ戻す。
方針：反対の逆操作の自然性と反転した切断の式を使い、係数の宇宙移送を消す。
規約：右端と同じ全 Hom の共通解像上の厳密な等式を示す。
使われ方：固定端点の補間を、既存の左右 Hom 区間比較の間のホモトピーとする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 元の左端模型は、既存の左 Hom の同じ coherent 単体の切断表示。 -/
lemma coherentTwoSidedHomLeftModel_cut {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) :
    coherentTwoSidedHomLeftModel σ t =
      (SimplicialNerve C).map (SimplexCategory.mkHom (coherentLeftPrismCut t)).op
        (coherentOppositeInverseSimplex (coherentHomComparisonSimplex
          (X := Opposite.op Y) (Y := Opposite.op X)
          (SSet.opObjEquiv ((edgewiseLeft _).app _ σ)))) := by
  rw [coherentTwoSidedHomLeftModel, coherentOppositeInverseSimplex_naturality,
    coherentLeftPrismCut_eq_reverse]
  rfl

/-- 補間の零段階は、元の左 Hom 区間の同じ切断単体そのもの。 -/
lemma coherentTwoSidedHomSimplex_zero_cut {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) :
    coherentTwoSidedHomSimplex σ t (OrderHom.const _ 0) =
      (SimplicialNerve C).map (SimplexCategory.mkHom (coherentLeftPrismCut t)).op
        (coherentOppositeInverseSimplex (coherentHomComparisonSimplex
          (X := Opposite.op Y) (Y := Opposite.op X)
          (SSet.opObjEquiv ((edgewiseLeft _).app _ σ)))) :=
  (coherentTwoSidedHomSimplex_zero_model σ t).trans (coherentTwoSidedHomLeftModel_cut σ t)

/-- 反転した係数の表示を揃えた左 Hom 区間は、元の同じ区間変換の族。 -/
lemma coherentLeftHomInterval_parameterized {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y : C) {A : SSet.{max u v}}
    (a : A ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y).op) :
    intervalMappingUncurry (a ≫ coherentCosliceFiberComparison X Y ≫
      cosliceFiberToIntervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y)) =
    (Δ[1] ◁ (a ≫ (uliftOppositeIso (SimplicialCategory.sHom X Y)).hom)) ≫
      coherentLeftHomInterval X Y := by
  rw [coherentLeftHomInterval, ← intervalMappingUncurry_precomp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- 補間段階の左端は、元の左 Hom 比較への実際の左射影の前合成そのもの。 -/
lemma coherentTwoSidedHomIntervalFamily_zero {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y : C) :
    prismEndpoint 0 _ ≫ coherentTwoSidedHomIntervalFamily X Y =
      (SSet.uliftFunctor.{v, u}).map (edgewiseLeft (SimplicialCategory.sHom X Y)) ≫
        coherentCosliceFiberComparison X Y ≫
          cosliceFiberToIntervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y) := by
  apply intervalMappingUncurry_injective _ _
  rw [intervalMappingUncurry_precomp, coherentTwoSidedHomIntervalFamily_uncurry,
    coherentLeftHomInterval_parameterized]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, σ⟩
  have h := coherentLeftHomInterval_evaluate X Y
    ((uliftOppositeIso (SimplicialCategory.sHom X Y)).hom.app (Opposite.op ⦋n⦌)
      (((SSet.uliftFunctor.{v, u}).map
        (edgewiseLeft (SimplicialCategory.sHom X Y))).app (Opposite.op ⦋n⦌) σ)) t
  exact (coherentTwoSidedHomSimplex_zero_cut σ.down
    (stdSimplex.objEquiv t).toOrderHom).trans h.symm

/-- 同じ共通 Hom 上で、元の左右 Hom 区間比較を結ぶ固定端点のホモトピー。 -/
def coherentTwoSidedHomIntervalHomotopy {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y : C) :
    SSet.Homotopy
      ((SSet.uliftFunctor.{v, u}).map (edgewiseLeft (SimplicialCategory.sHom X Y)) ≫
        coherentCosliceFiberComparison X Y ≫
          cosliceFiberToIntervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y))
      ((SSet.uliftFunctor.{v, u}).map (edgewiseRight (SimplicialCategory.sHom X Y)) ≫
        coherentHomComparison X Y ≫
          pinchedHomToIntervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y)) where
  h := (β_ _ _).hom ≫ coherentTwoSidedHomIntervalFamily X Y
  h₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro σ
    exact congrArg (fun f => f.app d σ) (coherentTwoSidedHomIntervalFamily_zero X Y)
  h₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro σ
    exact congrArg (fun f => f.app d σ) (coherentTwoSidedHomIntervalFamily_one X Y)
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories
