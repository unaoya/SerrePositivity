module

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredCompletedCylinder
public import SerrePositivity.KST.LocalizingInvariants.KanCylinderComparisonExtension

/-!
概要：元の亜群化評価の単位 Homotopy で、実円柱の商像を境界上の元の商射へ合わせる。
方針：始面と指定部分円柱の貼り合わせ上で同じ実族を作り、同じ全単位を前合成する。
規約：単位を独立に選び直さず、元の completionComparison と実境界を保持する。
使われ方：商 core 全円柱との境界付き比較の始域。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet
open CategoryTheory.CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.LocalizingInvariants

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}
  {G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj}
  {r : VerdierFiniteMappingCoconeRecovery h D z S a f}
  {U : VerdierRecoveredQuotientCoconeCylinder r G}

local notation "P" => S.toSSet ⊗ (Δ[1] : SSet)
local notation "J" => join (Δ[n] : SSet) Δ[0]

variable {c : VerdierRecoveredInitialComparison r U}

/-- 同じ元の評価像と単位 Homotopy で結ばれ、実境界では元の商射と厳密一致する全族。 -/
structure VerdierCompletedCylinderImage (X : VerdierRecoveredCompletedCylinder c) where
  whole : K ⊗ (Δ[1] : SSet.{u}) ⟶
    (quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj) : SSet.{u})
  homotopy : SSet.Homotopy
    (X.homotopy.h ≫ relativeFirstRowSimplexCompletionComparison q (n + 1)) whole
  start_eq : (SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ whole =
    c.simplexFamily ≫ relativeFirstRowSimplexQuotient q (n + 1)
  boundary_eq : (S.ι ▷ (Δ[1] : SSet.{u})) ≫ whole =
    r.simplexCylinder ≫ relativeFirstRowSimplexQuotient q (n + 1)
  start_unit_eq : ((SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷
      (Δ[1] : SSet.{u})) ≫ homotopy.h =
    (c.simplexFamily ▷ (Δ[1] : SSet.{u})) ≫
      (FunctorIso.simplicialHomotopy
        (relativeFirstRowSimplexCompletionComparison_unitIso q (n + 1))).h
  boundary_unit_eq : ((S.ι ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h =
    (r.simplexCylinder ▷ (Δ[1] : SSet.{u})) ≫
      (FunctorIso.simplicialHomotopy
        (relativeFirstRowSimplexCompletionComparison_unitIso q (n + 1))).h

/-- 元の全単位の前合成を使い、完成像を元の実商境界へ同時に合わせる。 -/
lemma exists_verdierCompletedCylinderImage (X : VerdierRecoveredCompletedCylinder c) :
    Nonempty (VerdierCompletedCylinderImage X) := by
  let E := (relativeFirstRowSimplex q (n + 1) : SSet.{u})
  let Z := (quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj) : SSet.{u})
  let Q := relativeFirstRowSimplexQuotient q (n + 1)
  let e := groupoidCompletionMap E
  let p := relativeFirstRowSimplexCompletionComparison q (n + 1)
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) S.ι
    (stdSimplex.δ (1 : Fin 2))
  have hL : pp.inl ≫ pp.ι = K ◁ stdSimplex.δ (1 : Fin 2) := pp.inl_ι
  have hR : pp.inr ≫ pp.ι = S.ι ▷ (Δ[1] : SSet.{u}) := pp.inr_ι
  have : Mono (Arrow.mk S.ι).hom := inferInstanceAs (Mono S.ι)
  have : Mono (Arrow.mk (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1])).hom :=
    inferInstanceAs (Mono (stdSimplex.δ (1 : Fin 2)))
  have : Mono pp.ι :=
    CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.instMonoHomObjArrowFunctorPushoutProduct
      (X := Arrow.mk S.ι) (Y := Arrow.mk (stdSimplex.δ (1 : Fin 2)))
  have hface : S.toSSet ◁ stdSimplex.δ (1 : Fin 2) =
      fst S.toSSet (Δ[0] : SSet.{u}) ≫ (SSet.ι₀ : S.toSSet ⟶ P) := by
    rw [stdSimplex.δ_one_eq_const]
    rfl
  have hc : (S.ι ▷ (Δ[0] : SSet.{u})) ≫
      (fst K (Δ[0] : SSet.{u}) ≫ c.simplexFamily) =
      (S.toSSet ◁ stdSimplex.δ (1 : Fin 2)) ≫ r.simplexCylinder := by
    rw [whiskerRight_fst_assoc, c.simplexFamily_boundary, hface, Category.assoc]
  let R : pp.pt ⟶ E := pp.isPushout.desc
    (fst K (Δ[0] : SSet.{u}) ≫ c.simplexFamily) r.simplexCylinder hc
  have hRl : pp.inl ≫ R = fst K (Δ[0] : SSet.{u}) ≫ c.simplexFamily :=
    pp.isPushout.inl_desc _ _ _
  have hRr : pp.inr ≫ R = r.simplexCylinder := pp.isPushout.inr_desc _ _ _
  have hXraw : pp.ι ≫ X.homotopy.h = R ≫ e := by
    apply pp.isPushout.hom_ext
    · calc
        _ = (K ◁ stdSimplex.δ (1 : Fin 2)) ≫ X.homotopy.h := by
          rw [← Category.assoc, hL]
        _ = fst K (Δ[0] : SSet.{u}) ≫ (c.simplexFamily ≫ e) :=
          HomotopyEndpointComparison.face_zero X.homotopy
        _ = _ := by
          simpa only [Category.assoc] using (congrArg (fun t => t ≫ e) hRl).symm
    · calc
        _ = (S.ι ▷ (Δ[1] : SSet.{u})) ≫ X.homotopy.h := by
          rw [← Category.assoc, hR]
        _ = r.simplexCylinder ≫ e := X.boundary_eq
        _ = _ := by rw [← Category.assoc, hRr]
  have hX : pp.ι ≫ (X.homotopy.h ≫ p) = R ≫ (e ≫ p) := by
    simpa only [Category.assoc] using congrArg (fun t => t ≫ p) hXraw
  let Hunit := FunctorIso.simplicialHomotopy
    (relativeFirstRowSimplexCompletionComparison_unitIso q (n + 1))
  let Hraw := functorHomotopyPrecomp Hunit R
  let H : SSet.Homotopy (pp.ι ≫ (X.homotopy.h ≫ p)) (R ≫ Q) :=
    { h := Hraw.h, h₀ := Hraw.h₀.trans hX.symm, h₁ := Hraw.h₁, rel := Hraw.rel }
  have hZ : modelCategoryQuillen.J.rlp (terminal.from Z) :=
    (modelCategoryQuillen.fibration_iff _).mp inferInstance
  obtain ⟨V, hV, HV, hHV⟩ := KanMonoEndpointExtension.exists_from_zero pp.ι hZ
    (X.homotopy.h ≫ p) (R ≫ Q) H
  have hstart : (K ◁ stdSimplex.δ (1 : Fin 2)) ≫ V =
      fst K (Δ[0] : SSet.{u}) ≫ c.simplexFamily ≫ Q := by
    calc
      _ = (pp.inl ≫ pp.ι) ≫ V := congrArg (fun t => t ≫ V) hL.symm
      _ = _ := by rw [Category.assoc, hV, ← Category.assoc, hRl, Category.assoc]
  have hstart' : (SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ V = c.simplexFamily ≫ Q := by
    rw [← LargeParameterHomotopy.section_zero K, Category.assoc, hstart]
    rfl
  have hboundary : (S.ι ▷ (Δ[1] : SSet.{u})) ≫ V = r.simplexCylinder ≫ Q := by
    calc
      _ = (pp.inr ≫ pp.ι) ≫ V := congrArg (fun t => t ≫ V) hR.symm
      _ = _ := by rw [Category.assoc, hV, ← Category.assoc, hRr]
  have hunit (T : SSet.{u}) (j : T ⟶ pp.pt) :
      ((j ≫ pp.ι) ▷ (Δ[1] : SSet.{u})) ≫ HV.h =
        ((j ≫ R) ▷ (Δ[1] : SSet.{u})) ≫ Hunit.h := by
    rw [comp_whiskerRight, Category.assoc, hHV]
    change (j ▷ (Δ[1] : SSet.{u})) ≫ (R ▷ (Δ[1] : SSet.{u})) ≫ Hunit.h = _
    rw [← comp_whiskerRight_assoc]
  have hsUnit : ((SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷
      (Δ[1] : SSet.{u})) ≫ HV.h = (c.simplexFamily ▷ (Δ[1] : SSet.{u})) ≫ Hunit.h := by
    have hz := hunit K (LargeParameterHomotopy.vertexSection K ≫ pp.inl)
    have hl : (LargeParameterHomotopy.vertexSection K ≫ pp.inl) ≫ pp.ι =
        (SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) := by
      rw [Category.assoc, hL, LargeParameterHomotopy.section_zero]
    have hr : (LargeParameterHomotopy.vertexSection K ≫ pp.inl) ≫ R = c.simplexFamily := by
      rw [Category.assoc, hRl, ← Category.assoc]
      rfl
    simpa only [hl, hr] using hz
  have hbUnit : ((S.ι ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ HV.h =
      (r.simplexCylinder ▷ (Δ[1] : SSet.{u})) ≫ Hunit.h := by
    simpa only [hR, hRr] using hunit P pp.inr
  exact ⟨⟨V, HV, hstart', hboundary, hsUnit, hbUnit⟩⟩

end SerrePositivity.KST.LocalizingInvariants
