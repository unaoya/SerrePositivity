module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.MappingSpaceMap
public import SerrePositivity.InfinityCategories.PinchedHom.Basic
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationCocone

/-!
概要：元の coherent な余錐のパラメータを制限しても点ごとの余極限性は保たれる。
方針：前合成後の評価を元の像の点での評価へ厳密に同定する。
規約：元の余錐の全単体を保持。使われ方：filtered 交換の形状同型不変性と有限接着。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 全余錐の射が厳密に一致すれば元の余極限性も一致する。 -/
lemma isColimitCone_iff_of_coconeMap_eq {J X : SSet.{u}} {p q : J ⟶ X}
    (c : JoinCocone p) (d : JoinCocone q) (h : c.val = d.val) :
    IsColimitCone c ↔ IsColimitCone d := by
  have hp : p = q := c.property.symm.trans
    ((congrArg (fun k => joinInl J Δ[0] ≫ k) h).trans d.property)
  subst q
  have hc : c = d := Subtype.ext h
  rw [hc]

/-- パラメータの前合成後の評価は、その元の像の点での評価。 -/
lemma functorCoconePrecomp_evaluate {A B X : SSet.{u}} (f : A ⟶ B) (a : A _⦋0⦌) :
    (pre f).app X ≫ evaluateFunctorAt a =
      evaluateFunctorAt (Y := X) (f.app (Opposite.op ⦋0⦌) a) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  change F.app (Opposite.op ⦋n⦌) (𝟙 _) (f.app _ (PinchedHom.constant a n)) = _
  rw [pinchedConstant_map]
  rfl

/-- 元の余錐全体を同じパラメータの前合成で制限する。 -/
def reindexFunctorCocone {J K L X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : JoinCocone p) (f : L ⟶ K) : JoinCocone (p ≫ (pre f).app X) :=
  mapJoinCocone ((pre f).app X) c

/-- 元の点ごとの余極限余錐は、任意のパラメータの前合成後も点ごとの余極限。 -/
lemma IsPointwiseColimitCone.reindex {J K L X : SSet.{u}}
    {p : J ⟶ (ihom K).obj X} {c : JoinCocone p} (hc : IsPointwiseColimitCone c)
    (f : L ⟶ K) : IsPointwiseColimitCone (reindexFunctorCocone c f) := by
  intro l
  apply (isColimitCone_iff_of_coconeMap_eq _
    (evaluateFunctorCocone c (f.app (Opposite.op ⦋0⦌) l)) ?_).mpr
    (hc (f.app (Opposite.op ⦋0⦌) l))
  change (c.val ≫ (pre f).app X) ≫ evaluateFunctorAt l =
    c.val ≫ evaluateFunctorAt (f.app (Opposite.op ⦋0⦌) l)
  rw [Category.assoc, functorCoconePrecomp_evaluate]

/-- 制限した余錐の頂点も元の頂点の同じ前合成である。 -/
lemma reindexFunctorCocone_vertex {J K L X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : JoinCocone p) (f : L ⟶ K) :
    (reindexFunctorCocone c f).vertex = ((pre f).app X).app (Opposite.op ⦋0⦌) c.vertex := rfl

end SerrePositivity.InfinityCategories.F2
