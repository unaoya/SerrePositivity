module
public import SerrePositivity.HomologicalAlgebra.DoldKanGammaMap
public import SerrePositivity.HomologicalAlgebra.NormalizedMooreMap
/-!
概要：指定Dold–Kan余単位の逆射を元のKaroubi模型の逆射として計算する。
方針：Moore包含を後合成し、Karoubi単位の自然性と正規化射影で打ち消す。
規約：IS-W2 B02の係数移送の証明分割。指定余単位を別の同型で置き換えない。
使われ方：HA 1.2.4、Γ余積比較と正規化比較の同じHom随伴の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory AlgebraicTopology AlgebraicTopology.DoldKan
open CategoryTheory.Idempotents
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Abelian C]
/-- 元の指定余単位の逆射は、Moore包含の後で同じKaroubi模型の逆射になる。 -/
theorem doldKanCounitInv_inclusion (K : ChainComplex C ℕ) :
    (Abelian.DoldKan.equivalence.counitIso.inv.app K) ≫
      inclusionOfMooreComplexMap ((Abelian.DoldKan.Γ : ChainComplex C ℕ ⥤ _).obj K) =
      (N₁Γ₀.inv.app K).f := by
  simp only [Abelian.DoldKan.equivalence, Equivalence.changeFunctor,
    Idempotents.DoldKan.equivalence_counitIso]
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app]
  simp [Abelian.DoldKan.comparisonN, Idempotents.DoldKan.η,
    Compatibility.equivalenceCounitIso, Category.assoc]
  have h : N₁Γ₀.inv.app K ≫
      (N₁_iso_normalizedMooreComplex_comp_toKaroubi C).hom.app (Abelian.DoldKan.Γ.obj K) =
      (toKaroubi (ChainComplex C ℕ)).map
        ((N₁Γ₀.inv.app K).f ≫ PInftyToNormalizedMooreComplex (Abelian.DoldKan.Γ.obj K)) := by
    rfl
  erw [← Functor.map_comp_assoc, h]
  erw [← (toKaroubiEquivalence (ChainComplex C ℕ)).unitIso.hom.naturality_assoc]
  erw [Iso.hom_inv_id_app_assoc]
  dsimp only [Functor.id_map]
  erw [Category.assoc, PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
  exact Karoubi.comp_p (N₁Γ₀.inv.app K)
end SerrePositivity.HomologicalAlgebra
