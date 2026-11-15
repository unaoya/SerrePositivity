module
public import SerrePositivity.HomologicalAlgebra.DoldKanCounitMooreInclusion
/-!
概要：指定正規化比較とΓ余積比較が同じDold–Kan余単位を保つことを示す。
方針：Moore包含で比較し、Γの非退化和因子と指定正規化射影で計算する。
規約：IS-W2 B02の係数移送の証明分割。元の二比較を変えない。
使われ方：HA 1.2.4、図式圏と点ごとの指定Hom随伴の両立。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
open CategoryTheory Limits Opposite AlgebraicTopology AlgebraicTopology.DoldKan
open CategoryTheory.Idempotents
open scoped Simplicial
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
/-- Karoubi模型の元の逆射は指定Γ余積比較と可換。 -/
theorem doldKanKaroubiCounitInv_map (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ) :
    (F.mapHomologicalComplex (.down ℕ)).map (N₁Γ₀.inv.app K).f ≫
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app (Abelian.DoldKan.Γ.obj K) =
    (N₁Γ₀.inv.app ((F.mapHomologicalComplex (.down ℕ)).obj K)).f ≫
      (alternatingFaceMapComplex D).map (gammaMapIso F K).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, alternatingFaceMapComplexCompMapHomologicalComplexIso,
    NatIso.ofComponents_hom_app, HomologicalComplex.Hom.isoOfComponents_hom_f,
    Iso.refl_hom]
  erw [Category.comp_id]
  change F.map ((N₁Γ₀.inv.app K).f.f n) =
    (N₁Γ₀.inv.app ((F.mapHomologicalComplex (.down ℕ)).obj K)).f.f n ≫
      (gammaMapIso F K).hom.app (op ⦋n⦌)
  simp only [N₁Γ₀_inv_app_f_f, SimplicialObject.Splitting.toKaroubiNondegComplexIsoN₁_hom_f_f]
  erw [PInfty_on_Γ₀_splitting_summand_eq_self K,
    PInfty_on_Γ₀_splitting_summand_eq_self ((F.mapHomologicalComplex (.down ℕ)).obj K)]
  simp only [SimplicialObject.Splitting.cofan_inj_id]
  change F.map (Sigma.ι (Γ₀.Obj.summand K (op ⦋n⦌))
      (SimplicialObject.Splitting.IndexSet.id (op ⦋n⦌))) =
    Sigma.ι (Γ₀.Obj.summand ((F.mapHomologicalComplex (.down ℕ)).obj K) (op ⦋n⦌))
      (SimplicialObject.Splitting.IndexSet.id (op ⦋n⦌)) ≫
      sigmaComparison F (Γ₀.Obj.summand K (op ⦋n⦌))
  exact (ι_comp_sigmaComparison F _ _).symm
/-- 二つの指定係数比較は元のDold–Kan余単位の逆射と厳密に可換。 -/
theorem doldKanCounitInv_map (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ) :
    (F.mapHomologicalComplex (.down ℕ)).map (Abelian.DoldKan.equivalence.counitIso.inv.app K) ≫
      normalizedMooreMapHom F (Abelian.DoldKan.Γ.obj K) =
    Abelian.DoldKan.equivalence.counitIso.inv.app
        ((F.mapHomologicalComplex (.down ℕ)).obj K) ≫
      (normalizedMooreComplex D).map (gammaMapIso F K).hom := by
  apply (cancel_mono (inclusionOfMooreComplexMap (Abelian.DoldKan.Γ.obj K ⋙ F))).mp
  have hL : ((F.mapHomologicalComplex (.down ℕ)).map
        (Abelian.DoldKan.equivalence.counitIso.inv.app K) ≫
      normalizedMooreMapHom F (Abelian.DoldKan.Γ.obj K)) ≫
        inclusionOfMooreComplexMap (Abelian.DoldKan.Γ.obj K ⋙ F) =
      (F.mapHomologicalComplex (.down ℕ)).map (N₁Γ₀.inv.app K).f ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app (Abelian.DoldKan.Γ.obj K) := by
    rw [Category.assoc, normalizedMooreMapHom_inclusion, ← Category.assoc,
      ← Functor.map_comp, doldKanCounitInv_inclusion]
  have hR := congrArg (fun h =>
    Abelian.DoldKan.equivalence.counitIso.inv.app
      ((F.mapHomologicalComplex (.down ℕ)).obj K) ≫ h)
    ((inclusionOfMooreComplex D).naturality (gammaMapIso F K).hom)
  have hE := congrArg (fun h => h ≫ (alternatingFaceMapComplex D).map (gammaMapIso F K).hom)
    (doldKanCounitInv_inclusion ((F.mapHomologicalComplex (.down ℕ)).obj K))
  calc
    _ = (F.mapHomologicalComplex (.down ℕ)).map (N₁Γ₀.inv.app K).f ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app (Abelian.DoldKan.Γ.obj K) := hL
    _ = (N₁Γ₀.inv.app ((F.mapHomologicalComplex (.down ℕ)).obj K)).f ≫
        (alternatingFaceMapComplex D).map (gammaMapIso F K).hom := doldKanKaroubiCounitInv_map F K
    _ = Abelian.DoldKan.equivalence.counitIso.inv.app
          ((F.mapHomologicalComplex (.down ℕ)).obj K) ≫
        inclusionOfMooreComplexMap
          ((Abelian.DoldKan.Γ : ChainComplex D ℕ ⥤ _).obj
            ((F.mapHomologicalComplex (.down ℕ)).obj K)) ≫
        (alternatingFaceMapComplex D).map (gammaMapIso F K).hom := by
      simpa only [Category.assoc] using hE.symm
    _ = _ := by simpa only [inclusionOfMooreComplex, Category.assoc] using hR.symm
end SerrePositivity.HomologicalAlgebra
