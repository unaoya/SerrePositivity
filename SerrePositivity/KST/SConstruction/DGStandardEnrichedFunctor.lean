module
public import SerrePositivity.KST.SConstruction.DGStandardHomComposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplicialCategory

/-! # 厳密 dg 関手の標準 DK 単体的豊穣関手
概要：元の dg 関手を、標準 DK Hom を持つ単体的圏間の厳密な豊穣関手へ移す。
方針：全単体の作用を束ね、既存の単位・AW 合成保存を適用する。
規約：標準 DK の非離散 Hom を保持する。使われ方：γ1 の関手性への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
  {E : Type w} [DGCategory A E] {B : Type t} [DGCategory A B]

/-- 厳密 dg 関手による、標準 DK 単体的圏の厳密な単体的豊穣関手。 -/
def dgStandardEnrichedFunctor (F : DGFunctor A D E) :
    EnrichedFunctor SSet.{u} (ClosedCategory A D) (ClosedCategory A E) where
  obj x := ForgetEnrichment.of (Complex A) (F.obj x)
  map x y := dgStandardHomMap F x y
  map_id x := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    exact dgStandardSimplexMap_unit F x n.unop.len
  map_comp x y z := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    exact dgStandardSimplexMap_aw F s.2 s.1

/-- dg 恒等関手は標準 DK の全単体をそのまま回収する。 -/
lemma dgStandardSimplexMap_id {x y : D} {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x y n) :
    dgStandardSimplexMap (DGFunctor.id D) f = f := by
  apply Subtype.ext
  funext i
  rfl

/-- 元の dg 関手の合成は、標準 DK の全単体上で厳密な合成を回収する。 -/
lemma dgStandardSimplexMap_comp (F : DGFunctor A D E) (G : DGFunctor A E B)
    {x y : D} {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x y n) :
    dgStandardSimplexMap (F.comp G) f = dgStandardSimplexMap G (dgStandardSimplexMap F f) := by
  apply Subtype.ext
  funext i
  rfl

/-- dg 恒等関手の標準 DK 豊穣関手は、元の単体的圏の恒等関手。 -/
lemma dgStandardEnrichedFunctor_id :
    dgStandardEnrichedFunctor (DGFunctor.id (A := A) D) =
      EnrichedFunctor.id SSet.{u} (ClosedCategory A D) := by
  apply EnrichedFunctor.ext SSet (fun _ => rfl)
  intro x y
  rw [eqToHom_refl, Category.comp_id]

/-- dg 合成は、標準 DK 豊穣関手の合成として厳密に回収される。 -/
lemma dgStandardEnrichedFunctor_comp (F : DGFunctor A D E) (G : DGFunctor A E B) :
    dgStandardEnrichedFunctor (F.comp G) =
      EnrichedFunctor.comp SSet.{u} (dgStandardEnrichedFunctor F)
        (dgStandardEnrichedFunctor G) := by
  apply EnrichedFunctor.ext SSet (fun _ => rfl)
  intro x y
  rw [eqToHom_refl, Category.comp_id]

end SerrePositivity.KST.SConstruction
