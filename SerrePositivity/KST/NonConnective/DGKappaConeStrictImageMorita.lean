module
public import SerrePositivity.KST.NonConnective.DGKappaConeExtensionNaturality
public import SerrePositivity.InfinityCategories.Derived.DGModuleMoritaInfinity
public import SerrePositivity.InfinityCategories.F2.Presentable.CompactEquivalenceUniverse
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulCalculus
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence

/-!
概要：元の実導来延長が同値なら、代表化した同じ κ-cone 関手も全 ∞ 圏同値となる。
方針：実導来包含の自然性で全 Hom を反映し、逆像の κ-compact 性と I.covers で頂点を回収する。
規約：同じ strict image の実関手を使う。全入力高次作用や商の同値は別工程。
使われ方：K-7 e の任意 Morita 入力射の実 cone 段での保存。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R]
  (C D : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [Small.{u} D] (f : DGFunctor R C D)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R C κ) (J : DGKappaConeInput R D κ)
  (e : DGModuleStrictImage R C D (dgModuleExtension R C D f) I.objects J.objects)

/-- 同じ実導来延長の充満忠実性を、元の実 cone 関手へ反映する。 -/
theorem dgKappaConeStrictImage_isFullyFaithful
    (hf : IsFullyFaithful (dgModuleExtensionInfinity R C D f)) :
    IsFullyFaithful (dgNerve.map (e.functor R C D _ I.objects J.objects)) := by
  have h := (FunctorIso.isFullyFaithful_iff
    (dgKappaConeStrictImageDerivedSquare R C D f I J e)).mp
      (I.derivedFullyFaithful.comp hf)
  exact J.derivedFullyFaithful.cancel_right h

/-- κ-compact な逆像を元の I の実代表で回収し、同じ cone 射の本質的全射性を得る。 -/
theorem dgKappaConeStrictImage_isEssentiallySurjective
    (hf : IsQCatEquivalence (dgModuleExtensionInfinity R C D f)) :
    IsEssentiallySurjective (dgNerve.map (e.functor R C D _ I.objects J.objects)) := by
  intro y
  obtain ⟨N, rfl⟩ := DGNerve.Simplex.vertexEquiv.symm.surjective y
  let z := (dgKappaConeDerivedComparison R D J).app (Opposite.op ⦋0⦌)
    (DGNerve.Simplex.vertex N)
  have hz : F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ z :=
    J.kappaCompact N.val N.property
  let E := hf.choose
  let x := E.inv.app (Opposite.op ⦋0⦌) z
  have hx : F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ x :=
    F2.Presentable.isKappaCompact_image_of_equivalence_universe E.symm z hz
  obtain ⟨M, hM, ⟨h⟩⟩ := I.covers x hx
  let a : (dgNerve R (DGKappaCone R C I)) _⦋0⦌ :=
    DGNerve.Simplex.vertex (⟨M, hM⟩ : DGKappaCone R C I)
  have h₀ : VertexIso ((dgKappaConeDerivedComparison R C I).app (Opposite.op ⦋0⦌) a) x := h
  have h₁ := (VertexIso.map h₀ E.hom) ≪≫ E.invHomIso.app z
  have h₂ := (dgKappaConeStrictImageDerivedSquare R C D f I J e).app a
  refine ⟨a, ⟨J.derivedFullyFaithful.preimageVertexIso ?_⟩⟩
  exact h₂.symm ≪≫ h₁

/-- 元の導来延長が同値なら、同じ実 cone 関手も全写像空間と全頂点で同値。 -/
theorem dgKappaConeStrictImage_isQCatEquivalence
    (hf : IsQCatEquivalence (dgModuleExtensionInfinity R C D f)) :
    IsQCatEquivalence (dgNerve.map (e.functor R C D _ I.objects J.objects)) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (dgKappaConeStrictImage_isFullyFaithful R C D f I J e hf.isFullyFaithful)
    (dgKappaConeStrictImage_isEssentiallySurjective R C D f I J e hf)

/-- 元の実主導来 Morita 射は、同じ κ と strict image の cone 作用で同値となる。 -/
theorem dgKappaConeStrictImage_isQCatEquivalence_of_morita
    [(dgDerivedExtension R C D f).IsEquivalence] :
    IsQCatEquivalence (dgNerve.map (e.functor R C D _ I.objects J.objects)) :=
  dgKappaConeStrictImage_isQCatEquivalence R C D f I J e
    (dgModuleExtensionInfinity_isQCatEquivalence_of_morita R C D f)

end SerrePositivity.KST.NonConnective
