module

public import SerrePositivity.InfinityCategories.F1.CoherentVertices
public import SerrePositivity.InfinityCategories.F1.CoherentTwoSidedHomNaturality
public import SerrePositivity.InfinityCategories.F1.MappingSpaceIntervalComparison

/-!
概要：左右を補間する族の二つの対象の境界を固定し、区間変換の空間へ持ち上げる。
方針：対象ラベルが定値のとき同じ標準頂点を回収し、区間方向で curry する。
規約：補間段階と全 Hom のパラメーターをともに保持する。
使われ方：左右の区間族の間の、固定端点を持つ実際の補間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 対象のラベルが全て零なら、補間段階に関わらず元の始域の定値単体。 -/
lemma coherentTwoSidedHomSimplex_source {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (s : Fin (n + 1) →o Fin 2) :
    coherentTwoSidedHomSimplex σ (OrderHom.const _ 0) s =
      (SimplicialNerve C).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
        (coherentNerveVertex X) := by
  apply EnrichedFunctor.ext SSet
    (F := coherentTwoSidedHomSimplex σ (OrderHom.const _ 0) s)
    (G := (SimplicialNerve C).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (coherentNerveVertex X)) (fun _ => rfl)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  apply SSet.hom_ext
  intro d
  rfl

/-- 対象のラベルが全て一なら、補間段階に関わらず元の標的の定値単体。 -/
lemma coherentTwoSidedHomSimplex_target {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (s : Fin (n + 1) →o Fin 2) :
    coherentTwoSidedHomSimplex σ (OrderHom.const _ 1) s =
      (SimplicialNerve C).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
        (coherentNerveVertex Y) := by
  apply EnrichedFunctor.ext SSet
    (F := coherentTwoSidedHomSimplex σ (OrderHom.const _ 1) s)
    (G := (SimplicialNerve C).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (coherentNerveVertex Y)) (fun _ => rfl)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  apply SSet.hom_ext
  intro d
  rfl

/-- 主区間と、補間段階・全 Hom のパラメーターに分けた同じ正方形の族。 -/
def coherentTwoSidedHomSquare {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    (Δ[1] : SSet.{max u v}) ⊗ (Δ[1] ⊗ (SSet.uliftFunctor.{v, u}).obj
      (edgewiseSubdivision (SimplicialCategory.sHom X Y))) ⟶ SimplicialNerve C :=
  (α_ _ _ _).inv ≫ coherentTwoSidedHomFamily X Y

/-- 同じ正方形の族の始域側は、全段階・全 Hom 上で元の頂点に厳密に定値。 -/
lemma coherentTwoSidedHomSquare_zero {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    prismEndpoint 0 _ ≫ coherentTwoSidedHomSquare X Y =
      SSet.const (coherentNerveVertex X) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, σ⟩
  exact coherentTwoSidedHomSimplex_source σ.down (stdSimplex.objEquiv s).toOrderHom

/-- 同じ正方形の族の標的側も、全段階・全 Hom 上で元の頂点に厳密に定値。 -/
lemma coherentTwoSidedHomSquare_one {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    prismEndpoint 1 _ ≫ coherentTwoSidedHomSquare X Y =
      SSet.const (coherentNerveVertex Y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, σ⟩
  exact coherentTwoSidedHomSimplex_target σ.down (stdSimplex.objEquiv s).toOrderHom

/-- 全 Hom と補間段階を、元の二頂点を固定した実際の区間変換空間へ写す。 -/
def coherentTwoSidedHomIntervalFamily {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    (Δ[1] : SSet.{max u v}) ⊗ (SSet.uliftFunctor.{v, u}).obj
      (edgewiseSubdivision (SimplicialCategory.sHom X Y)) ⟶
      intervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y) :=
  intervalMappingCurryOfEndpoints (coherentTwoSidedHomSquare X Y)
    (coherentTwoSidedHomSquare_zero X Y) (coherentTwoSidedHomSquare_one X Y)

/-- 固定端点の区間変換の族を展開すると、元の同じ補間正方形の族そのもの。 -/
lemma coherentTwoSidedHomIntervalFamily_uncurry {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y : C) :
    intervalMappingUncurry (coherentTwoSidedHomIntervalFamily X Y) =
      coherentTwoSidedHomSquare X Y :=
  intervalMappingUncurry_curryOfEndpoints _ _ _

end SerrePositivity.InfinityCategories
