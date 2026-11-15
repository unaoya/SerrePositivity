module
public import SerrePositivity.HomologicalAlgebra.DoldKanCoefficientCounit
/-!
概要：指定正規化比較とΓ比較をDold–Kanの同じHom随伴へ移す。
方針：既存の余単位両立と随伴Hom同値の公式を使う。
規約：IS-W2 B02の係数移送則の証明分割。二比較と元の随伴を保持する。
使われ方：HA 1.2.4、点ごとのΓと図式圏の正規化Homの指定射の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
open CategoryTheory AlgebraicTopology
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
/-- 同じ余単位の順射にも指定係数比較の両立を適用する。 -/
theorem doldKanCounit_map (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ) :
    normalizedMooreMapHom F (Abelian.DoldKan.Γ.obj K) ≫
      (normalizedMooreComplex D).map (gammaMapIso F K).inv ≫
      Abelian.DoldKan.equivalence.counitIso.hom.app
        ((F.mapHomologicalComplex (.down ℕ)).obj K) =
    (F.mapHomologicalComplex (.down ℕ)).map (Abelian.DoldKan.equivalence.counitIso.hom.app K) := by
  apply (cancel_epi ((F.mapHomologicalComplex (.down ℕ)).map
    (Abelian.DoldKan.equivalence.counitIso.inv.app K))).mp
  have h := congrArg (fun t => t ≫
      (normalizedMooreComplex D).map (gammaMapIso F K).inv ≫
      Abelian.DoldKan.equivalence.counitIso.hom.app
        ((F.mapHomologicalComplex (.down ℕ)).obj K)) (doldKanCounitInv_map F K)
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app] at h
  calc
    _ = 𝟙 _ := by simpa only [Functor.id_obj, Category.assoc] using h
    _ = _ := by rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
/-- 指定された正規化・Γの二比較を使うと元のHom随伴の値が一致する。 -/
theorem doldKanHomEquiv_map (F : C ⥤ D) [F.Additive]
    (W : SimplicialObject C) (K : ChainComplex C ℕ)
    (f : (normalizedMooreComplex C).obj W ⟶ K) :
    (Abelian.DoldKan.equivalence : SimplicialObject D ≌ ChainComplex D ℕ).toAdjunction.homEquiv
      (W ⋙ F) ((F.mapHomologicalComplex (.down ℕ)).obj K)
      ((normalizedMooreMapIso F W).inv ≫ (F.mapHomologicalComplex (.down ℕ)).map f) ≫
        (gammaMapIso F K).hom =
    Functor.whiskerRight
      ((Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction.homEquiv
        W K f) F := by
  apply (cancel_mono (gammaMapIso F K).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply ((Abelian.DoldKan.equivalence : SimplicialObject D ≌ ChainComplex D ℕ).toAdjunction.homEquiv
    (W ⋙ F) ((F.mapHomologicalComplex (.down ℕ)).obj K)).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply, Functor.map_comp]
  apply (cancel_epi (normalizedMooreMapIso F W).hom).mp
  let g : W ⟶ (Abelian.DoldKan.Γ : ChainComplex C ℕ ⥤ _).obj K :=
    (Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction.homEquiv
    W K f
  have hg := ((Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction.homEquiv
    W K).symm_apply_apply f
  change (normalizedMooreComplex C).map g ≫
    Abelian.DoldKan.equivalence.counitIso.hom.app K = f at hg
  simp only [Category.assoc, Equivalence.toAdjunction_counit, Equivalence.counit,
    Abelian.DoldKan.equivalence_functor, Abelian.DoldKan.N]
  change (normalizedMooreMapIso F W).hom ≫
      ((normalizedMooreMapIso F W).inv ≫ (F.mapHomologicalComplex (.down ℕ)).map f) =
    (normalizedMooreMapIso F W).hom ≫
      ((normalizedMooreComplex D).map (Functor.whiskerRight g F) ≫
        (normalizedMooreComplex D).map (gammaMapIso F K).inv ≫
          Abelian.DoldKan.equivalence.counitIso.hom.app
            ((F.mapHomologicalComplex (.down ℕ)).obj K))
  rw [Iso.hom_inv_id_assoc]
  rw [← Category.assoc]
  erw [← normalizedMooreMapHom_naturality F g]
  erw [Category.assoc, doldKanCounit_map, ← Functor.map_comp, hg]
end SerrePositivity.HomologicalAlgebra
