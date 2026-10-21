module

public import SerrePositivity.InfinityCategories.F1.CocartesianOriginalCellOverNaturalityEndpoints
public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexLocalComparison

/-!
概要：共有セルへの区間 Hom の制限を同じ名前の射で照合する。
方針：同じ底上の射を明示し、cospan の二脚の射と一致させる。
規約：元の制限写像を変更しない。
使われ方：巨大な指定同型を展開せず、その終点の制限を照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]

/-- 元の指定共有セルへ制限する区間 Hom の射。 -/
def cocartesianCellOverHomRestrictionMap (l : A ⥤ D) (k : D ⥤ C) (v : A ⥤ C)
    (h : l ⋙ k = v) (p q : CocartesianFibrationCategory (nerve C)) :=
  intervalDiagramOverPre
    (B := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (X := CatInfinity.{u})
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
    (a := Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap v)))
    (b := Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k)))
    (uliftOverMorphism (cocartesianCellOverMap l k v h))

/-- cospan の最初の脚は、同じ指定共有セルの制限写像。 -/
lemma cocartesianTwoSimplexLocalTarget_firstMap
    (k : ULift.{u} (Fin 3) ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl =
    cocartesianCellOverHomRestrictionMap
      (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
      (cocartesianTwoSimplexFirstCell k) (cocartesianTwoSimplexSharedCell k) rfl p q := rfl

/-- cospan の次の脚も、同じ指定共有セルの制限写像。 -/
lemma cocartesianTwoSimplexLocalTarget_secondMap
    (k : ULift.{u} (Fin 3) ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr =
    cocartesianCellOverHomRestrictionMap
      (cocartesianSimplexCellIndex (SimplexCategory.δ (1 : Fin 2)))
      (cocartesianTwoSimplexSecondCell k) (cocartesianTwoSimplexSharedCell k)
      (cocartesianTwoSimplexSharedCell_second k) p q := rfl

end SerrePositivity.InfinityCategories
