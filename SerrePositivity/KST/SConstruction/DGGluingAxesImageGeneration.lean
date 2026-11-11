module
public import SerrePositivity.KST.SConstruction.DGGluingAxesPerfectGeneration
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Derived.Functor

/-! # 元の実 dg 関手像における二軸生成判定
概要：元の gluing を送る同じ dg 関手の像は、元の二軸の像から生成される。
方針：D の導来延長・代表加群の指定比較を使い、実二軸三角形を送る。
規約：商・局所化の普遍性は入力しない。使われ方：既存 D 商射の具体的生成性への適用。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (E : Type z) [DGCategory R E] [Small.{u} E]
  (F : DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) E)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "Q" => moduleToDerived R E
local instance : (dgDerivedExtension R G E F).CommShift ℤ :=
  dgDerivedExtensionCommShift R G E F
local instance : (dgDerivedExtension R G E F).IsTriangulated :=
  dgDerivedExtensionIsTriangulated R G E F

include hc hd in
/-- 同じ二軸の像を含む三角的条件は、元の dg 関手の全対象像の代表を含む。 -/
lemma dgGluingAxes_image_representable_mem
    (P : ObjectProperty (DerivedModuleCategory R E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms]
    (hR : ∀ d : D, P ((Q).obj (ForgetEnrichment.of (Complex R)
      (representable R (F.obj (dgGluingRightAxisObject R C D M zc d))))))
    (hL : ∀ c : C, P ((Q).obj (ForgetEnrichment.of (Complex R)
      (representable R (F.obj (dgGluingLeftAxisObject R C D M zd c))))))
    (X : G) : P ((Q).obj (ForgetEnrichment.of (Complex R) (representable R (F.obj X)))) := by
  let P' := P.inverseImage (dgDerivedExtension R G E F)
  have : P'.IsTriangulated := by dsimp [P']; infer_instance
  have : P'.IsClosedUnderIsomorphisms := by dsimp [P']; infer_instance
  have hr : ∀ d : D, P' ((moduleToDerived R G).obj (ForgetEnrichment.of (Complex R)
      (representable R (dgGluingRightAxisObject R C D M zc d)))) := fun d =>
    P.prop_of_iso (dgDerivedExtensionRepresentableIso R G E F
      (dgGluingRightAxisObject R C D M zc d)).symm (hR d)
  have hl : ∀ c : C, P' ((moduleToDerived R G).obj (ForgetEnrichment.of (Complex R)
      (representable R (dgGluingLeftAxisObject R C D M zd c)))) := fun c =>
    P.prop_of_iso (dgDerivedExtensionRepresentableIso R G E F
      (dgGluingLeftAxisObject R C D M zd c)).symm (hL c)
  exact P.prop_of_iso (dgDerivedExtensionRepresentableIso R G E F X)
    (dgGluingAxes_representable_mem R C D M zc hc zd hd P' hr hl X)

include hc hd in
/-- 同じ実関手像が生成する Perf の包含は、元の二軸像だけで判定できる。 -/
lemma dgGluingPerfectOver_image_le_iff_axes
    (P : ObjectProperty (DerivedModuleCategory R E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] [P.IsStableUnderRetracts] :
    modulePerfectOver R E (Set.range F.obj) ≤ P ↔
      (∀ d : D, P ((Q).obj (ForgetEnrichment.of (Complex R)
        (representable R (F.obj (dgGluingRightAxisObject R C D M zc d)))))) ∧
      (∀ c : C, P ((Q).obj (ForgetEnrichment.of (Complex R)
        (representable R (F.obj (dgGluingLeftAxisObject R C D M zd c)))))) := by
  rw [modulePerfectOver_le_iff_generators R E P]
  constructor
  · intro h
    exact ⟨fun d => h _ ⟨_, rfl⟩, fun c => h _ ⟨_, rfl⟩⟩
  · rintro ⟨hR, hL⟩ y ⟨X, rfl⟩
    exact dgGluingAxes_image_representable_mem R C D M zc hc zd hd E F P hR hL X

end SerrePositivity.KST.SConstruction
