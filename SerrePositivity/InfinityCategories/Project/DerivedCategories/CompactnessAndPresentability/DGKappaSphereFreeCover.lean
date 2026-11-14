module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereFreeFamily

/-!
概要：κ 未満自由 sphere の実小代表族と、射影的代表集合の導来 ∞ 比較を構成する。
方針：小さい ordinal 添字と実直和表示、β5 の全関手比較を保持する。
規約：全共変 Hom による κ-compact 性や全 κ-compact 被覆はここでは結論しない。
使われ方：K-7 に供給する実 κ-compact dg 小模型の出発点。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma exists_kappa_initialSegment_equiv {κ : Cardinal.{u}} (I : Type u)
    (hI : Cardinal.mk I < κ) : ∃ a : κ.ord.ToType, Nonempty (Set.Iio a ≃ I) := by
  have ho : (Cardinal.mk I).ord < Ordinal.type (α := κ.ord.ToType) (· < ·) := by
    simpa only [Ordinal.type_toType] using Cardinal.ord_strictMono hI
  let a : κ.ord.ToType := Ordinal.enum (α := κ.ord.ToType) (· < ·) ⟨(Cardinal.mk I).ord, ho⟩
  have ha : Ordinal.typein (α := κ.ord.ToType) (· < ·) a = (Cardinal.mk I).ord :=
    Ordinal.typein_enum (α := κ.ord.ToType) (· < ·) ho
  have hc : Cardinal.mk (Set.Iio a) = Cardinal.mk I := by
    calc
      _ = (Ordinal.typein (α := κ.ord.ToType) (· < ·) a).card :=
        (Ordinal.card_typein a).symm
      _ = (Cardinal.mk I).ord.card := congrArg Ordinal.card ha
      _ = Cardinal.mk I := Cardinal.card_ord _
  exact ⟨a, Cardinal.eq.mp hc⟩

lemma dgKappaSphereFreeModule_covers {κ : Cardinal.{u}}
    (I : Type u) (object : I → D) (degree : I → ℤ) (hI : Cardinal.mk I < κ) :
    ∃ i : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R D i ≅
        ∐ (fun j : I ↦ freeSphere R D (object j) (degree j))) := by
  obtain ⟨a, ⟨e⟩⟩ := exists_kappa_initialSegment_equiv I hI
  let i : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ :=
    ⟨a, fun j ↦ (equivShrink D (object (e j)), degree (e j))⟩
  refine ⟨i, ⟨Sigma.whiskerEquiv (Equiv.ulift.trans e) (fun j ↦ ?_)⟩⟩
  dsimp only [i, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule]
  simp only [Equiv.symm_apply_apply]
  exact Iso.refl _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
