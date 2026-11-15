module

public import SerrePositivity.AlgebraicGeometry.FiniteOpenModels

/-!
概要：有限アトラスの全重なりの開の模型と等式を、一つの共通する段へそろえる。
方針：各チャートで有限個の開を降ろし、さらに有限 cone で共通段を取る。
規約：元の重なりの準コンパクト性を、準分離性から供給する。
使われ方：G2 の同じ係数段上の実際の gluing datum。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v w

/-- 準分離空間の準コンパクトな開チャートの二重交叉は準コンパクト。 -/
theorem isCompact_atlas_overlap {ι : Type v} {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (U : ι → Scheme.{u}) [∀ i, CompactSpace (U i)]
    (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i)] (i k : ι) :
    IsCompact (j i ⁻¹ᵁ (j k).opensRange : Set (U i)) :=
  QuasiCompact.isCompact_preimage _ (j k).opensRange.isOpen (isCompact_range (j k).continuous)

variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  {ι : Type v} [Finite ι] {κ : Type w} [Finite κ]
  (D : ι → J ⥤ Scheme.{u}) (c : ∀ i, Cone (D i)) (hc : ∀ i, IsLimit (c i))
  [∀ a {i j} (f : i ⟶ j), IsAffineHom ((D a).map f)]
  [∀ a i, CompactSpace ((D a).obj i)] [∀ a i, QuasiSeparatedSpace ((D a).obj i)]

include hc

/-- 有限個のチャートの各有限個の開の模型を、一つの共通する段へそろえる。 -/
theorem exists_finite_atlas_opens_model_of_isLimit
    (U : ∀ i, κ → (c i).pt.Opens) (hU : ∀ i a, IsCompact (U i a : Set (c i).pt)) :
    ∃ (j : J) (V : ∀ i, κ → ((D i).obj j).Opens),
      ∀ i a, IsCompact (V i a : Set ((D i).obj j)) ∧ (c i).π.app j ⁻¹ᵁ V i a = U i a := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  choose j V hV using fun i ↦ exists_finite_opens_model_of_isLimit (D i) (c i) (hc i) (U i) (hU i)
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  let q (i : ι) : k ⟶ j i := (hk (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).some
  refine ⟨k, fun i a ↦ (D i).map (q i) ⁻¹ᵁ V i a, ?_⟩
  intro i a
  refine ⟨QuasiCompact.isCompact_preimage _ (V i a).isOpen (hV i a).1, ?_⟩
  rw [← Scheme.Hom.comp_preimage, (c i).w, (hV i a).2]

/-- 有限アトラスの全チャートの有限個の開の等式を、一つの共通する後の段へ降ろす。 -/
theorem exists_finite_atlas_open_equalities_of_isLimit {j : J}
    (U V : ∀ i, κ → ((D i).obj j).Opens)
    (hU : ∀ i a, IsCompact (U i a : Set ((D i).obj j)))
    (hV : ∀ i a, IsCompact (V i a : Set ((D i).obj j)))
    (heq : ∀ i a, (c i).π.app j ⁻¹ᵁ U i a = (c i).π.app j ⁻¹ᵁ V i a) :
    ∃ (k : J) (q : k ⟶ j), ∀ i a, (D i).map q ⁻¹ᵁ U i a = (D i).map q ⁻¹ᵁ V i a := by
  have hsingle (z : ι × κ) :
      ∃ (k : J) (q : k ⟶ j), (D z.1).map q ⁻¹ᵁ U z.1 z.2 = (D z.1).map q ⁻¹ᵁ V z.1 z.2 :=
    exists_map_preimage_eq_map_preimage (D z.1) (c z.1) (hc z.1) (hU z.1 z.2) (hV z.1 z.2)
      (heq z.1 z.2)
  choose k q hq using hsingle
  obtain ⟨l, g, a, ha⟩ := IsCofiltered.wideCospan q
  refine ⟨l, g, ?_⟩
  intro i b
  have h := congrArg (fun W ↦ (D i).map (a (i, b)) ⁻¹ᵁ W) (hq (i, b))
  simpa only [← Scheme.Hom.comp_preimage, ← Functor.map_comp, ha] using h

end SerrePositivity.AlgebraicGeometry
