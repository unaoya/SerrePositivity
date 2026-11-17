module

public import SerrePositivity.AlgebraicGeometry.SectionAdaptedAffineCover
public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalDescent
public import SerrePositivity.HomologicalAlgebra.Cech.Composition

/-!
概要：元の切断を持つ射の有限アフィン被覆のČech totalの完全性。
方針：各有限交叉族のアフィン余積に、切断に適合する基底の有限アフィン余積を写す。
規約：忠実平坦性を使うのは基底のアフィン開被覆だけで、非アフィンなΓには使わない。
使われ方：切断を持つ射の普遍Čech降下（承認済み計画F07）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.isDefEq.respectTransparency false

/-- 切断を持つ元の射の同じ有限アフィン被覆のČech totalは完全。 -/
theorem section_perfectCechTupleTotal_acyclic
    {R : Type u} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated g] [QuasiCompact g]
    [LocallyOfFinitePresentation g] (s : Spec (CommRingCat.of R) ⟶ Y)
    (hs : s ≫ g = 𝟙 _) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleDouble g U p hp hR) (.up ℕ)).Acyclic := by
  classical
  haveI : Y.IsSeparated := ⟨by rw [← terminal.comp_from g]; infer_instance⟩
  apply schemePerfectCechTupleDouble_acyclic_of_augmented_rows
  intro k
  let W (a : Fin (k+1) → ι) : Y.Opens := ⨅ r, U (a r)
  have hW (a : Fin (k+1) → ι) : IsAffineOpen (W a) :=
    openIntersectionFamily_isAffine U hU a
  have hcW : (⨆ a, W a) = ⊤ := openIntersectionFamily_iSup U hcU
  obtain ⟨n, V, ρ, hV, hcV, hle⟩ := exists_section_adapted_affine_cover g s hs W hcW
  haveI (a : Fin (k+1) → ι) : IsAffine (W a).toScheme := hW a
  haveI (j : Fin n) : IsAffine (V j).toScheme := hV j
  let w := Sigma.desc (fun a : Fin (k+1) → ι ↦ (W a).ι ≫ g)
  let v := Sigma.desc (fun j : Fin n ↦ (V j).ι)
  let a := Sigma.desc (fun j : Fin n ↦
    s.resLE (W (ρ j)) (V j) (hle j) ≫ Sigma.ι (fun b ↦ (W b).toScheme) (ρ j))
  have ha : a ≫ w = v := by
    apply Sigma.hom_ext
    intro j
    dsimp only [a, w, v]
    rw [← Category.assoc, Sigma.ι_comp_desc, Category.assoc,
      Sigma.ι_comp_desc, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
      Category.assoc, hs, Category.comp_id, Sigma.ι_comp_desc]
  haveI : Surjective v := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⨆ j, V j := by rw [hcV]; trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨j, by rw [Scheme.Opens.range_ι]; exact hj⟩
  haveI : Flat v := by dsimp only [v]; infer_instance
  let A := Scheme.Γ.obj (op (Spec (CommRingCat.of R)))
  let B : Under A := Under.mk (Scheme.Γ.map w.op)
  let D : Under A := Under.mk (Scheme.Γ.map v.op)
  let r : B ⟶ D := Under.homMk (Scheme.Γ.map a.op) (by
    change Scheme.Γ.map w.op ≫ Scheme.Γ.map a.op = Scheme.Γ.map v.op
    rw [← Scheme.Γ.map_comp, ← op_comp, ha])
  have hf : (Scheme.Γ.map v.op).hom.FaithfullyFlat := by
    rw [Scheme.Γ_map_op]
    exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine v).mp
      ⟨inferInstance, inferInstance⟩
  haveI : Module.FaithfullyFlat A D.right := hf
  have hB : SerrePositivity.Cech.IsCechExact (Arrow.mk B.hom) :=
    (SerrePositivity.Cech.isCechExact_baseChange_iff D.right B).mp
      (SerrePositivity.Cech.isCechExact_baseChange_of_map B D r)
  let hA : (p : A) = 0 :=
    schemeScalarPresheaf_primeCast (Spec (CommRingCat.of R)) (𝟙 _) p hR (op ⊤)
  have hS : (p : B.right) = 0 := by
    rw [← map_natCast B.hom.hom, hA, map_zero]
  haveI : IsFiltered (AsSmall.{u} ℕ) :=
    IsFiltered.of_equivalence (AsSmall.equiv : ℕ ≌ AsSmall.{u} ℕ)
  have hcol := SerrePositivity.Cech.isCechExact_colimit
    (frobeniusArrowSmallDiagram (Arrow.mk B.hom) p hp hA hS) (fun _ ↦ hB)
  let eF := frobeniusArrowSmallColimitIso (Arrow.mk B.hom) p hp hA hS
  let G : Arrow CommRingCat.{u} ⥤ CosimplicialObject.Augmented CommRingCat.{u} :=
    CosimplicialObject.augmentedCechConerve
  have hF := (SerrePositivity.Cech.ringCechExact_iff_of_iso (G.mapIso eF)).mpr hcol
  have hx := (frobeniusAugmentedRingCoefficients_exact_iff
    (Arrow.mk B.hom) p hp hA hS).mpr hF
  let hN : ∀ m : SimplexCategory,
      (p : (rectangularPerfectRowGammaFunctor g U k).obj m) = 0 := fun m ↦ by
    have hz := congrArg
      (Scheme.Γ.map ((Arrow.mk w).augmentedCechNerve.hom.app (op m)).op).hom hA
    simpa only [map_natCast, map_zero] using hz
  have hy := (ringCechExact_iff_integer_acyclic _).mp hx
  let e := affineGammaPerfectAugmentedCoefficientsIso w p hp hA hN ≪≫
    rectangularPerfectAugmentedRowIso g U p hp hR k hA hN
  intro m
  exact (hy m).of_iso (SerrePositivity.Cech.augmentedCochain.mapIso e)

end SerrePositivity.AlgebraicGeometry
