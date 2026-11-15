module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealLimitModel

/-!
概要：逆極限上の有限型イデアルの閉部分スキームを、有限表示の閉部分として有限段へ降ろす。
方針：有限型イデアルの模型と comapIso の実際の pullback の比較を使う。
規約：Stacks 0B8W (3) のイデアル模型からの閉部分の比較。基底は qcqs。
使われ方：A07 の閉包絡の有限表示模型と G2 の模型。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 有限型イデアルの閉部分スキームを、有限段の有限表示な閉部分の実際の底変換として表示する。 -/
theorem exists_finitePresentation_closed_model_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (K : c.pt.IdealSheafData) (hK : IsFiniteTypeIdealSheaf K) :
    ∃ (j : J) (L : (D.obj j).IdealSheafData), IsFiniteTypeIdealSheaf L ∧
      LocallyOfFinitePresentation L.subschemeι ∧
      ∃ e : K.subscheme ≅ pullback (c.π.app j) L.subschemeι,
        e.hom ≫ pullback.fst _ _ = K.subschemeι := by
  obtain ⟨j, L, hL, heq⟩ := exists_finiteType_ideal_model_of_isLimit D c hc K hK
  refine ⟨j, L, hL, locallyOfFinitePresentation_subschemeι_of_finiteType L hL, ?_⟩
  rw [← heq]
  exact ⟨L.comapIso (c.π.app j), L.comapIso_hom_fst (c.π.app j)⟩

end SerrePositivity.AlgebraicGeometry
