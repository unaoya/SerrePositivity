module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaPresentedFreeCoproduct
/-!
概要：κ 未満自由表示の空ラベルを実零対象として指定する。
方針：κ の中の空初期区間を選び、空のセル集合で全 Hom の零性を証明する。
規約：選択は κ だけに依存し、dg 関手は同じ空ラベルを厳密に保つ。
使われ方：16時間試作の零演算と前三角性への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable {κ : Cardinal.{u}} (hκ : 0 < κ)

def dgKappaFreeEmptyOrdinal : κ.ord.ToType :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.exists_kappa_initialSegment_equiv PEmpty.{u + 1} (by simpa using hκ)).choose

def dgKappaFreeEmptyEquiv : Set.Iio (dgKappaFreeEmptyOrdinal hκ) ≃ PEmpty.{u + 1} :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.exists_kappa_initialSegment_equiv PEmpty.{u + 1}
    (by simpa using hκ)).choose_spec

variable (D : Type v) [Small.{u} D]
def dgKappaPresentedFreeZero : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ :=
  ⟨dgKappaFreeEmptyOrdinal hκ, fun j => (dgKappaFreeEmptyEquiv hκ j).elim⟩

variable {R : Type u} [CommRing R] {E : Type w}
  [DGCategory R D] [DGCategory R E] [Small.{u} E]

lemma dgKappaPresentedFreeObjectMap_zero (F : DGFunctor R D E) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeObjectMap R F (dgKappaPresentedFreeZero hκ D) =
      dgKappaPresentedFreeZero hκ E := by
  apply congrArg (fun f : Set.Iio (dgKappaFreeEmptyOrdinal hκ) → Shrink.{u} E × ℤ =>
    (⟨⟨dgKappaFreeEmptyOrdinal hκ, f⟩⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject E κ))
  funext j
  exact (dgKappaFreeEmptyEquiv hκ j).elim

lemma dgKappaPresentedFreeZero_isZero :
    IsZero (ForgetEnrichment.of (Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ (dgKappaPresentedFreeZero hκ D))) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply Sigma.hom_ext
  intro j
  exact (dgKappaFreeEmptyEquiv hκ j.down).elim

end SerrePositivity.InfinityCategories.Project.DerivedCategories
