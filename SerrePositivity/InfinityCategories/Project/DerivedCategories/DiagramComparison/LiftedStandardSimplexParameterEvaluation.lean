module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LiftedStandardSimplexHomEvaluation

/-!
概要：指定持ち上げ標準単体のYonedaパラメータと元の単体的射の像を照合する。
方針：同じ標準単体Hom評価の自然性と両逆射則を使う。
規約：元の宇宙同型・全高次単体を保持する既存構成の評価・自然性則。
使われ方：HA 1.2.4、IS-W2 B02の実DKパラメータと自由tensor Homの成分照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory

/-- 同じ標準単体Hom評価は任意の元の単体的射の後合成と可換。 -/
theorem liftedStandardSimplexHomIso_postcomp {Z Z' : SSet.{u}} (f : Z ⟶ Z')
    (n : SimplexCategory)
    (t : (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⟶ Z) :
    (liftedStandardSimplexHomIso Z').hom.app (Opposite.op n) (t ≫ f) =
      f.app (Opposite.op n) ((liftedStandardSimplexHomIso Z).hom.app (Opposite.op n) t) := by
  rw [liftedStandardSimplexHomIso_hom_apply, liftedStandardSimplexHomIso_hom_apply]
  rfl

/-- 同じ宇宙同型を通した指定Yonedaパラメータの評価は元の全単体そのもの。 -/
theorem liftedStandardSimplexHomIso_yoneda_apply (Z : SSet.{u}) (n : SimplexCategory)
    (α : Z.obj (Opposite.op n)) :
    (liftedStandardSimplexHomIso Z).hom.app (Opposite.op n)
      (liftedStandardSimplexIso.{u}.hom.app n ≫ SSet.yonedaEquiv.symm α) = α := by
  have hi := ConcreteCategory.congr_hom
    (Iso.inv_hom_id_app (liftedStandardSimplexHomIso Z) (Opposite.op n)) α
  change (liftedStandardSimplexHomIso Z).hom.app (Opposite.op n)
    ((liftedStandardSimplexHomIso Z).inv.app (Opposite.op n) α) = α at hi
  have h := liftedStandardSimplexHomIso_yoneda Z n
    ((liftedStandardSimplexHomIso Z).inv.app (Opposite.op n) α)
  rw [hi] at h
  exact (congrArg (fun t => (liftedStandardSimplexHomIso Z).hom.app (Opposite.op n) t) h).trans hi

/-- 指定Yonedaパラメータに元の射を作用させた評価は同じ全単体の射の像。 -/
theorem liftedStandardSimplexHomIso_yoneda_postcomp {Z Z' : SSet.{u}} (f : Z ⟶ Z')
    (n : SimplexCategory) (α : Z.obj (Opposite.op n)) :
    (liftedStandardSimplexHomIso Z').hom.app (Opposite.op n)
      ((liftedStandardSimplexIso.{u}.hom.app n ≫ SSet.yonedaEquiv.symm α) ≫ f) =
        f.app (Opposite.op n) α := by
  rw [liftedStandardSimplexHomIso_postcomp, liftedStandardSimplexHomIso_yoneda_apply]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
