module
public import SerrePositivity.KST.Fibration.WeakStringGappedPostcomposition
public import SerrePositivity.KST.Fibration.WeakStringRelativeDiagonal

/-! # 元の二重単体・対角の交換同型は包含側の完全関手を厳密に保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 全 W 列と相対 S の元の二重単体の交換は、元の包含側の後合成と可換。 -/
lemma weakStringObjectRelativeIso_postcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    Functor.whiskerRight (weakStringStablePostcomp f q) objectSConstructionFunctor ≫
      (weakStringObjectRelativeIso q).hom =
        (weakStringObjectRelativeIso (f ≫ q : A ⟶ C)).hom ≫
          (flipFunctor _ _ _).map (relativeSimplicialFunctorMap f q.hom) := by
  apply NatTrans.ext
  funext m
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro v
  change SSet.yonedaEquiv (weakStringGappedRelativeMap q
    (((sEndofunctor n.unop.len).map (weakStringPostExact f q m.unop)).val.app
      (Opposite.op ⦋0⦌) v)) = _
  rw [weakStringGappedRelativeMap_postcomp, SSet.yonedaEquiv_comp]
  rfl

/-- 元の二重単体写像に関して、対角の方向交換の同型は自然。 -/
lemma simplicialDiagonalFlipIso_naturality {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (f : X ⟶ Y) :
    simplicialDiagonalFunctor.map ((flipFunctor _ _ _).map f) ≫
      (simplicialDiagonalFlipIso Y).hom =
        (simplicialDiagonalFlipIso X).hom ≫ simplicialDiagonalFunctor.map f := by
  apply NatTrans.ext
  funext n
  change (f.app n).app n ≫ 𝟙 _ = 𝟙 _ ≫ (f.app n).app n
  simp only [Category.comp_id, Category.id_comp]

/-- 元の相対 S 対角の厳密交換同型は、元の包含側の完全関手と可換。 -/
lemma weakStringObjectRelativeDiagonalIso_postcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    simplicialDiagonalFunctor.map
      (Functor.whiskerRight (weakStringStablePostcomp f q) objectSConstructionFunctor) ≫
      (weakStringObjectRelativeDiagonalIso q).hom =
        (weakStringObjectRelativeDiagonalIso (f ≫ q : A ⟶ C)).hom ≫
          simplicialDiagonalFunctor.map (relativeSimplicialFunctorMap f q.hom) := by
  change simplicialDiagonalFunctor.map
    (Functor.whiskerRight (weakStringStablePostcomp f q) objectSConstructionFunctor) ≫
      (simplicialDiagonalFunctor.map (weakStringObjectRelativeIso q).hom ≫ _) =
    (simplicialDiagonalFunctor.map (weakStringObjectRelativeIso (f ≫ q : A ⟶ C)).hom ≫ _) ≫ _
  rw [← Category.assoc, ← Functor.map_comp, weakStringObjectRelativeIso_postcomp,
    Functor.map_comp, Category.assoc, simplicialDiagonalFlipIso_naturality, ← Category.assoc]

end SerrePositivity.KST.Fibration
