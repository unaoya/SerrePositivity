module
public import SerrePositivity.KST.SConstruction.DGFunctorClosedComparison

/-! # 単位パラメータの全次数自然性からの閉比較の回収
概要：元の単位パラメータ自然変換から、同じ閉射族の全 Hom 可換式を回収する。
方針：左 unitor の逆を前合成し、元の単位 braiding と二つの unitor を消す。
規約：通常射の自然性で代用しない。使われ方：tensor 評価後の閉比較を合成する界面。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] {D : Type v} [DGCategory R D]
  {E : Type w} [DGCategory R E] (F G : DGFunctor R D E)

/-- 元の単位パラメータ変換と同じ閉射成分から、全 Hom の可換式を回収する。 -/
lemma dgClosedComparison_from_parameter
    (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R))) F G)
    (a : ∀ x : D, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
      ForgetEnrichment.of (Complex R) (G.obj x))
    (ha : ∀ x, τ.app x = ForgetEnrichment.homTo (Complex R) (a x)) (x y : D) :
    F.map x y ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
    G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
      (ForgetEnrichment.of (Complex R) (G.obj y)) := by
  have h := τ.naturality x y
  rw [ha x, ha y] at h
  change (β_ (𝟙_ (Complex R)) (x ⟶[Complex R] y)).hom ≫
    (F.map x y ⊗ₘ ForgetEnrichment.homTo (Complex R) (a y)) ≫
      eComp (Complex R) _ _ _ =
    (ForgetEnrichment.homTo (Complex R) (a x) ⊗ₘ G.map x y) ≫
      eComp (Complex R) _ _ _ at h
  have h' := congrArg (fun k => (λ_ (x ⟶[Complex R] y)).inv ≫ k) h
  rw [braiding_tensorUnit_left] at h'
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h'
  rw [rightUnitor_inv_comp_tensorHom_assoc, leftUnitor_inv_comp_tensorHom_assoc] at h'
  exact h'

end SerrePositivity.KST.SConstruction
