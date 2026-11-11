module

public import SerrePositivity.KST.NonConnective.BoundaryAdditivity

/-!
概要：S• 加法性の実射対の識別性と、二つの軸による群の分解。
方針：証明済みの全基点 π 同型から射対の単射性を取り出し、群の積を比較する。
規約：中央項の加法性を仮定せず、標準二軸の評価から導く。
使われ方：swindle の同じ連結 K 群の消去。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 実境界商 Kan 加法性の subobject・quotient は、正次数群の元を識別する。 -/
theorem boundaryKanAdditivityGroup_injective (r : ℕ) (X : StableModel.{u}) (n : ℕ) :
    Function.Injective
      ((pointedGroupMap n ((boundaryKanRealizationFunctor r).map (cofiberStableSubobject X))).prod
        (pointedGroupMap n ((boundaryKanRealizationFunctor r).map (cofiberStableQuotient X)))) := by
  intro a b h
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_bijective_of_piIsomorphism n
    (boundaryKanAdditivityMap r X).right (boundaryKanAdditivityMap_piIsomorphism r X)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)).injective
  apply pointedGroupProd_injective ((boundaryKanRealizationFunctor r).obj X)
    ((boundaryKanRealizationFunctor r).obj X) n
  apply Prod.ext
  · change pointedGroupMap n (PointedObject.prodFst _ _)
      (pointedGroupMap n (boundaryKanAdditivityMap r X) a) =
        pointedGroupMap n (PointedObject.prodFst _ _)
          (pointedGroupMap n (boundaryKanAdditivityMap r X) b)
    simpa only [← pointedGroupMap_comp, boundaryKanAdditivityMap,
      PointedObject.prodLift_fst, MonoidHom.prod_apply] using congrArg Prod.fst h
  · change pointedGroupMap n (PointedObject.prodSnd _ _)
      (pointedGroupMap n (boundaryKanAdditivityMap r X) a) =
        pointedGroupMap n (PointedObject.prodSnd _ _)
          (pointedGroupMap n (boundaryKanAdditivityMap r X) b)
    simpa only [← pointedGroupMap_comp, boundaryKanAdditivityMap,
      PointedObject.prodLift_snd, MonoidHom.prod_apply] using congrArg Prod.snd h

/-- 識別的な射対の二つの軸は、元の同じ群の全ての元を分解する。 -/
lemma additivityGroup_decomposition {G : Type u} {H : Type v} [Group G] [Group H]
    (p q : H →* G) (l r : G →* H) (hi : Function.Injective (p.prod q))
    (hpl : ∀ x, p (l x) = x) (hql : ∀ x, q (l x) = 1)
    (hpr : ∀ x, p (r x) = 1) (hqr : ∀ x, q (r x) = x) (x : H) :
    x = l (p x) * r (q x) := by
  apply hi
  apply Prod.ext
  · change p x = p (l (p x) * r (q x))
    rw [map_mul, hpl, hpr, mul_one]
  · change q x = q (l (p x) * r (q x))
    rw [map_mul, hql, hqr, one_mul]

/-- 中央項の射は、二つの標準軸での恒等性から加法性を持つ。 -/
lemma additivityGroup_middle {G : Type u} {H : Type v} [Group G] [Group H]
    (p q m : H →* G) (l r : G →* H) (hi : Function.Injective (p.prod q))
    (hpl : ∀ x, p (l x) = x) (hql : ∀ x, q (l x) = 1)
    (hpr : ∀ x, p (r x) = 1) (hqr : ∀ x, q (r x) = x)
    (hml : ∀ x, m (l x) = x) (hmr : ∀ x, m (r x) = x) (x : H) :
    m x = p x * q x := by
  have h := congrArg m (additivityGroup_decomposition p q l r hi hpl hql hpr hqr x)
  simpa only [map_mul, hml, hmr] using h

end SerrePositivity.KST.NonConnective
