module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaPresentedFreeLabelOperations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereFreeCover
public import Mathlib.SetTheory.Cardinal.Regular
/-!
概要：κ 未満自由表示の直和を、対象ラベルに依存しない添字表示で構成する。
方針：ordinal の族だけから平坦化の同値を保持し、同じ同値で全ラベルを並べる。
規約：dg 関手は添字表示を変更しない。実加群との比較は同型として保持する。
使われ方：16時間試作の κ-small 直和、特に可算直和の閉演算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded

/-- 平坦化の選択は対象ラベルを含まず、ordinal の族だけを参照する。 -/
structure DGKappaFreeSumShape {κ : Cardinal.{u}} {J : Type u}
    (a : J → κ.ord.ToType) where
  ordinal : κ.ord.ToType
  reindex : Set.Iio ordinal ≃ Σ j, Set.Iio (a j)

lemma dgKappaFreeSumShape_nonempty {κ : Cardinal.{u}} {J : Type u}
    (a : J → κ.ord.ToType) (hreg : κ.IsRegular) (hJ : Cardinal.mk J < κ) :
    Nonempty (DGKappaFreeSumShape a) := by
  have hsum : Cardinal.mk (Σ j, Set.Iio (a j)) < κ := by
    rw [Cardinal.mk_sigma]
    exact Cardinal.sum_lt_of_isRegular hreg hJ
      (fun j => by simpa using Cardinal.mk_Iio_lt (a j) (by simp))
  obtain ⟨b, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.exists_kappa_initialSegment_equiv _ hsum
  exact ⟨⟨b, e⟩⟩

variable {R : Type u} [CommRing R] {D : Type v} {E : Type w}
  [DGCategory R D] [DGCategory R E] [Small.{u} D] [Small.{u} E]
  {κ : Cardinal.{u}} {J : Type u}

/-- 指定した添字平坦化を用いる自由表示の直和。 -/
def dgKappaPresentedFreeSum (X : J → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ)
    (s : DGKappaFreeSumShape (fun j => (X j).label.1)) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ :=
  ⟨s.ordinal, fun k => (X (s.reindex k).1).label.2 (s.reindex k).2⟩

lemma dgKappaPresentedFreeObjectMap_sum (F : DGFunctor R D E)
    (X : J → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ)
    (s : DGKappaFreeSumShape (fun j => (X j).label.1)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeObjectMap R F (dgKappaPresentedFreeSum X s) =
      dgKappaPresentedFreeSum (fun j => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeObjectMap R F (X j)) s := rfl

/-- 表示の平坦化は、元の実加群直和をそのまま評価する。 -/
def dgKappaPresentedFreeSumIso (X : J → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ)
    (s : DGKappaFreeSumShape (fun j => (X j).label.1)) :
    ForgetEnrichment.of (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ (dgKappaPresentedFreeSum X s)) ≅
      ∐ (fun j => ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ (X j))) := by
  let g (j : J) (k : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeCells D (X j).label) :=
    freeSphere R D ((equivShrink D).symm ((X j).label.2 k.down).1)
      ((X j).label.2 k.down).2
  change (∐ (fun k : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeCells D (dgKappaPresentedFreeSum X s).label =>
    freeSphere R D ((equivShrink D).symm
      ((dgKappaPresentedFreeSum X s).label.2 k.down).1)
      ((dgKappaPresentedFreeSum X s).label.2 k.down).2)) ≅ ∐ (fun j => ∐ (g j))
  exact (Sigma.whiskerEquiv
    (g := fun p : Σ j, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeCells D (X j).label => g p.1 p.2)
    (Equiv.ulift.trans (s.reindex.trans (Equiv.sigmaCongrRight fun _ => Equiv.ulift.symm)))
    (fun _ => Iso.refl _)) ≪≫ (sigmaSigmaIso _ g).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
