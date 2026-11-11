module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Whiskering

/-!
概要：全ての有限単体集合を、同じ小さい宇宙の一つの図式型で同型まで符号化する。
方針：次数ごとの有限集合を FintypeCat の小さい骨格へ移し、全ての面・退化と自然同型を同時に保持する。
規約：コードは宇宙 u、実現は元の SSet u。各次数の全単射だけでなく図式全体の同型を与える。
使われ方：空間の共通の小さい compact 生成族。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 小さい有限集合骨格値の単体的図式の、元の宇宙の単体集合としての実現。 -/
def finiteSkeletonRealization (F : SimplexCategoryᵒᵖ ⥤ FintypeCat.Skeleton.{u}) : SSet.{u} :=
  F ⋙ FintypeCat.Skeleton.incl ⋙ forget FintypeCat

/-- 有限な実現を持つ全ての骨格値単体的図式。元の小さい宇宙内の一つの型。 -/
def FiniteSimplicialCode : Type u :=
  {F : SimplexCategoryᵒᵖ ⥤ FintypeCat.Skeleton.{u} // (finiteSkeletonRealization F).Finite}

/-- 同じ有限コードの元の単体集合としての実現。 -/
def FiniteSimplicialCode.realization (q : FiniteSimplicialCode.{u}) : SSet.{u} :=
  finiteSkeletonRealization q.val

instance (q : FiniteSimplicialCode.{u}) : q.realization.Finite := q.property

/-- 元の有限単体集合の同じ全単体を、有限集合の圏に束縛する。 -/
def finiteSimplicialFintypeDiagram (A : SSet.{u}) [A.Finite] :
    SimplexCategoryᵒᵖ ⥤ FintypeCat.{u} := by
  let (n : SimplexCategoryᵒᵖ) : Fintype (A.obj n) := Fintype.ofFinite _
  exact {
    obj n := FintypeCat.of (A.obj n)
    map f := FintypeCat.homMk (A.map f)
    map_id n := by
      apply FintypeCat.hom_ext
      intro x
      exact CategoryTheory.Functor.map_id_apply A n x
    map_comp f g := by
      apply FintypeCat.hom_ext
      intro x
      exact CategoryTheory.Functor.map_comp_apply A f g x }

/-- 元の有限単体集合の全図式を、同じ小さい有限集合骨格へ移す。 -/
def finiteSimplicialSkeletonDiagram (A : SSet.{u}) [A.Finite] :
    SimplexCategoryᵒᵖ ⥤ FintypeCat.Skeleton.{u} :=
  finiteSimplicialFintypeDiagram A ⋙ FintypeCat.Skeleton.equivalence.inverse

/-- 骨格へ移した元の全図式を実現すると、同じ元の有限単体集合と厳密に同型。 -/
def finiteSimplicialSkeletonIso (A : SSet.{u}) [A.Finite] :
    finiteSkeletonRealization (finiteSimplicialSkeletonDiagram A) ≅ A :=
  CategoryTheory.Functor.isoWhiskerRight
    (CategoryTheory.Functor.isoWhiskerLeft (finiteSimplicialFintypeDiagram A)
    FintypeCat.Skeleton.equivalence.counitIso) (forget FintypeCat)

/-- 元の任意の有限単体集合は、共通の小さい有限コード族の一つと全単体で同型。 -/
lemma exists_finiteSimplicialCode (A : SSet.{u}) [A.Finite] :
    ∃ q : FiniteSimplicialCode.{u}, Nonempty (q.realization ≅ A) := by
  let e := finiteSimplicialSkeletonIso A
  have h : (finiteSkeletonRealization (finiteSimplicialSkeletonDiagram A)).Finite :=
    (SSet.finite_iff_of_iso e).mpr inferInstance
  exact ⟨⟨finiteSimplicialSkeletonDiagram A, h⟩, ⟨e⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
