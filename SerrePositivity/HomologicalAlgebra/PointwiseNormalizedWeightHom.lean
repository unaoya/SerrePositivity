module
public import SerrePositivity.HomologicalAlgebra.PointwiseDoldKanHomEquiv
public import SerrePositivity.HomologicalAlgebra.PointwiseTruncationHomEquiv
public import SerrePositivity.HomologicalAlgebra.PointwiseTruncationGamma
public import SerrePositivity.HomologicalAlgebra.NormalizedWeightHom
/-!
概要：元の正規化重みHom同値を指定零延長・切断・Γ比較で点ごとに移す。
方針：元の二つのHom随伴を保ち、指定正規化比較の逆を前合成する。
規約：IS-W2 B02の同じ係数移送の証明分割。全図式射と全単体を保持する。
使われ方：HA 1.2.4、指定BK錐代表と自由鎖の全単体比較の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type*) [Category* J] (C : Type*) [Category* C] [Abelian C]
/-- 元の正規化Hom同値は元の零延長随伴とDold–Kan随伴の同じ合成。 -/
theorem normalizedWeightHomEquiv_asAdjunction
    (W : SimplicialObject C) (H : CochainComplex C ℤ)
    (f : ((normalizedMooreComplex C).obj W).extend ComplexShape.embeddingDownNat ⟶ H) :
    normalizedWeightHomEquiv W H f =
      (Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction.homEquiv
        W (H.truncLE' (ComplexShape.embeddingUpIntLE 0))
        ((negativeExtendTruncationAdjunction C).homEquiv _ H f) := by
  simp only [normalizedWeightHomEquiv, Equiv.trans_apply, negativeExtendTruncationAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl
/-- 元の切断Γ比較の順射を同じ二つの指定比較に括り直す。 -/
theorem pointwiseTruncationGammaIso_hom (H : CochainComplex (J ⥤ C) ℤ) :
    (pointwiseTruncationGammaIso J C).hom.app H =
      (pointwiseGammaIso J C).inv.app (H.truncLE' (ComplexShape.embeddingUpIntLE 0)) ≫
        ((Functor.whiskeringRight J (ChainComplex C ℕ) (SimplicialObject C)).obj
          Abelian.DoldKan.Γ).map ((pointwiseTruncationIso J C).hom.app H) := by
  simp only [pointwiseTruncationGammaIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom]
  change _ ≫ 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl
/-- 同じ実正規化重みHom同値は指定比較で点ごとの同じHom随伴に一致する。 -/
theorem pointwiseNormalizedWeightHomEquiv
    (W : SimplicialObject (J ⥤ C)) (H : CochainComplex (J ⥤ C) ℤ)
    (f : ((normalizedMooreComplex (J ⥤ C)).obj W).extend ComplexShape.embeddingDownNat ⟶ H) :
    (flipFunctor SimplexCategoryᵒᵖ J C).map (normalizedWeightHomEquiv W H f) ≫
      (pointwiseTruncationGammaIso J C).hom.app H =
    ((Adjunction.whiskerRight J
      (Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction).comp
        (Adjunction.whiskerRight J (negativeExtendTruncationAdjunction C))).homEquiv
      W.flip (complexOfFunctorsToFunctorToComplex.obj H)
      (((Functor.whiskeringRight J (ChainComplex C ℕ) (CochainComplex C ℤ)).obj
          (ComplexShape.embeddingDownNat.extendFunctor C)).map
        ((pointwiseMooreIso J C).inv.app W) ≫
        (pointwiseExtendIso J C ComplexShape.embeddingDownNat).inv.app
          ((normalizedMooreComplex (J ⥤ C)).obj W) ≫
        complexOfFunctorsToFunctorToComplex.map f) := by
  rw [normalizedWeightHomEquiv_asAdjunction]
  rw [pointwiseTruncationGammaIso_hom]
  rw [← Category.assoc, pointwiseDoldKanHomEquiv]
  erw [← Adjunction.homEquiv_naturality_right]
  erw [Category.assoc, pointwiseTruncationIso_homEquiv]
  erw [← Adjunction.homEquiv_naturality_left, Adjunction.comp_homEquiv]
  rfl
end SerrePositivity.HomologicalAlgebra
