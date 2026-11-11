module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FreeHomDegreeExt

/-! # 自由係数 dg 圏の各次数は単位と生成辺で決まる

概要：二辺以上の path summand は零であり、各次数の写像は単位と生成辺で決まる。
方針：生成辺の終点から出る quiver が零であることを tensor に移す。
規約：対象・Hom の独立宇宙を保つ。使われ方：係数評価間の全次数の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded HomologicalComplex
open scoped ZeroObject
variable (A : Type u) [CommRing A] (M : Complex A)

/-- 生成辺の終点から出る quiver 複体は零。 -/
lemma dgWalkingHomQuiver_fromTarget_zero (b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex.{v}) :
    IsZero (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomQuiver A M ⟨true⟩ b) := by
  rcases b with ⟨b⟩
  cases b <;> exact isZero_zero _

/-- 生成辺の終点から始まる非空辺 path の複体は零。 -/
lemma dgWalkingHomWord_fromTarget_zero (w : List _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex.{v})
    (y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex.{v}) :
    IsZero (FreeDGCategory.wordTensor A _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomQuiver A M)
      w ⟨true⟩ y) := by
  cases w with
  | nil => exact dgWalkingHomQuiver_fromTarget_zero A M y
  | cons b w =>
    exact (tensorRight _).map_isZero (dgWalkingHomQuiver_fromTarget_zero A M b)

/-- 内部頂点を一つ以上持つ path は、零の辺を必ず一つ含む。 -/
lemma dgWalkingHomWord_cons_zero (b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex.{v})
    (w : List _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex.{v}) (x y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex.{v}) :
    IsZero (FreeDGCategory.wordTensor A _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomQuiver A M)
      (b :: w) x y) := by
  rcases x with ⟨x⟩
  cases x with
  | true => exact (tensorRight _).map_isZero (dgWalkingHomQuiver_fromTarget_zero A M b)
  | false =>
    rcases b with ⟨b⟩
    cases b with
    | false => exact (tensorRight _).map_isZero (isZero_zero _)
    | true => exact (tensorLeft _).map_isZero (dgWalkingHomWord_fromTarget_zero A M w y)

/-- 自由係数 dg Hom の各次数の写像は、単位 path と一つの生成辺で決まる。 -/
lemma dgWalkingHomDegree_ext (x y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex.{v}) (k : ℤ)
    {N : ModuleCat.{u} A}
    {f g : (FreeDGCategory.homComplex A _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomQuiver A M) x y).X k
      ⟶ N}
    (hu : ∀ h : x = y,
      (FreeDGCategory.pathInclusion A _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomQuiver A M)
        x y (.inl ⟨h⟩)).f k ≫ f =
      (FreeDGCategory.pathInclusion A _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomQuiver A M)
        x y (.inl ⟨h⟩)).f k ≫ g)
    (he : (FreeDGCategory.edgeInclusion A _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomQuiver A M)
      x y).f k ≫ f =
      (FreeDGCategory.edgeInclusion A _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomQuiver A M)
        x y).f k ≫ g) : f = g := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.freeHomDegree_ext A _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomQuiver A M) x y k
  intro p
  cases p with
  | inl h => exact hu h.down
  | inr w =>
    cases w with
    | nil => exact he
    | cons b w =>
      exact ((HomologicalComplex.eval (ModuleCat A) (.up ℤ) k).map_isZero
        (dgWalkingHomWord_cons_zero A M b w x y)).eq_of_src _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
