module

public import SerrePositivity.AlgebraicGeometry.FiniteOpenModels

/-!
概要：極限で閉になった準コンパクト開を有限段でも閉にする。
方針：補開を降ろし、和と交叉の二つの式を共通段へ移す。
規約：Stacks 01ZP の開包含の場合の入力。係数射の忠実平坦性は要求しない。
使われ方：G2 の閉埋め込み性と固有性の降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits Topology
universe u

/-- 極限で閉になった準コンパクト開は、ある後の有限段でも閉になる。 -/
theorem exists_closed_open_preimage_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {i : J} (U : (D.obj i).Opens) (hU : IsCompact (U : Set (D.obj i)))
    (hclosed : IsClosed ((c.π.app i ⁻¹ᵁ U : c.pt.Opens) : Set c.pt)) :
    ∃ (j : J) (a : j ⟶ i), IsClosed (D.map a ⁻¹ᵁ U : Set (D.obj j)) := by
  classical
  letI : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  let W : c.pt.Opens := c.π.app i ⁻¹ᵁ U
  let V : c.pt.Opens := ⟨(W : Set c.pt)ᶜ, hclosed.isOpen_compl⟩
  obtain ⟨j, V₀, hV₀, heV⟩ := exists_preimage_eq D c hc V W.isOpen.isClosed_compl.isCompact
  obtain ⟨k, fi, fj, -⟩ := IsCofilteredOrEmpty.cone_objs i j
  let U' := D.map fi ⁻¹ᵁ U
  let V' := D.map fj ⁻¹ᵁ V₀
  have hU' : IsCompact (U' : Set (D.obj k)) := QuasiCompact.isCompact_preimage _ U.isOpen hU
  have hV' : IsCompact (V' : Set (D.obj k)) := QuasiCompact.isCompact_preimage _ V₀.isOpen hV₀
  have hu : c.π.app k ⁻¹ᵁ U' = W := by rw [← Scheme.Hom.comp_preimage, c.w]
  have hv : c.π.app k ⁻¹ᵁ V' = V := by rw [← Scheme.Hom.comp_preimage, c.w, heV]
  let L : Bool → (D.obj k).Opens := fun b ↦ if b then U' ⊔ V' else U' ⊓ V'
  let R : Bool → (D.obj k).Opens := fun b ↦ if b then ⊤ else ⊥
  have hL (b : Bool) : IsCompact (L b : Set (D.obj k)) := by
    cases b
    · exact hU'.inter_of_isOpen hV' U'.isOpen V'.isOpen
    · exact hU'.union hV'
  have hR (b : Bool) : IsCompact (R b : Set (D.obj k)) := by
    cases b
    · exact isCompact_empty
    · exact isCompact_univ
  have hEq (b : Bool) : c.π.app k ⁻¹ᵁ L b = c.π.app k ⁻¹ᵁ R b := by
    cases b <;> simp only [L, R, Bool.false_eq_true, ite_false, ite_true,
      Scheme.Hom.preimage_inf, Scheme.Hom.preimage_sup, Scheme.Hom.preimage_bot,
      Scheme.Hom.preimage_top, hu, hv]
    · ext x; simp [V]
    · ext x; simp [V]
  obtain ⟨l, a, ha⟩ := exists_finite_open_equalities_of_isLimit D c hc L R hL hR hEq
  let A := D.map a ⁻¹ᵁ U'
  let B := D.map a ⁻¹ᵁ V'
  have hd : A ⊓ B = ⊥ := by simpa only [L, R, Bool.false_eq_true, ite_false,
    Scheme.Hom.preimage_inf, Scheme.Hom.preimage_bot] using ha false
  have ht : A ⊔ B = ⊤ := by simpa only [L, R, ite_true,
    Scheme.Hom.preimage_sup, Scheme.Hom.preimage_top] using ha true
  have hcompl : (A : Set (D.obj l))ᶜ = (B : Set (D.obj l)) := by
    ext x
    have hx₁ : ¬ (x ∈ A ∧ x ∈ B) := by simpa using congrArg (fun Z : (D.obj l).Opens ↦ x ∈ Z) hd
    have hx₂ : x ∈ A ∨ x ∈ B := by simpa using congrArg (fun Z : (D.obj l).Opens ↦ x ∈ Z) ht
    constructor
    · exact fun h ↦ hx₂.resolve_left h
    · exact fun hb ha ↦ hx₁ ⟨ha, hb⟩
  have hop : IsOpen (A : Set (D.obj l))ᶜ := hcompl.symm ▸ B.isOpen
  have hA : IsClosed (A : Set (D.obj l)) := by
    simpa only [compl_compl] using hop.isClosed_compl
  refine ⟨l, a ≫ fi, ?_⟩
  simpa only [A, U', Functor.map_comp, Scheme.Hom.comp_preimage] using hA

end SerrePositivity.AlgebraicGeometry
