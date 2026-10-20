module
public import SerrePositivity.KST.SConstruction.DGFunctorHomUniversal

/-! # dg 関手の Hom end 上の厳密な前合成作用
概要：源への厳密 dg 関手は、元の全次数自然変換とその全パラメータへ作用する。
方針：全対象の評価を元の対象写像で制限し、全 Hom 射で自然性を前合成する。
規約：全次数の自然性と元のパラメータを保持する。使われ方：dg 入力の非離散 Hom。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] (B : Type t) [DGCategory A B] [Small.{u} B]
  (H : DGFunctor A B D)

omit [Small.{u} D] [Small.{u} B] in
/-- 全次数自然性を元の source Hom chain map で前合成した可換式。 -/
lemma dgFunctorParamPre_naturality {K : Complex A} {M N : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K M N) (x y : B) :
    (β_ K (x ⟶[Complex A] y)).hom ≫
      ((H.map x y ≫ M.map (H.obj x) (H.obj y)) ⊗ₘ τ.app (H.obj y)) ≫
        eComp (Complex A) (M.obj (H.obj x)) (M.obj (H.obj y)) (N.obj (H.obj y)) =
    (τ.app (H.obj x) ⊗ₘ (H.map x y ≫ N.map (H.obj x) (H.obj y))) ≫
      eComp (Complex A) (M.obj (H.obj x)) (N.obj (H.obj x)) (N.obj (H.obj y)) := by
  have h₀ : (β_ K (H.obj x ⟶[Complex A] H.obj y)).hom ≫
      (M.map (H.obj x) (H.obj y) ⊗ₘ τ.app (H.obj y)) ≫
        eComp (Complex A) (M.obj (H.obj x)) (M.obj (H.obj y)) (N.obj (H.obj y)) =
    (τ.app (H.obj x) ⊗ₘ N.map (H.obj x) (H.obj y)) ≫
      eComp (Complex A) (M.obj (H.obj x)) (N.obj (H.obj x)) (N.obj (H.obj y)) :=
    τ.naturality (H.obj x) (H.obj y)
  have h := congrArg (fun k => (𝟙 K ⊗ₘ H.map x y) ≫ k) h₀
  simp only [← Category.assoc] at h
  rw [BraidedCategory.braiding_naturality] at h
  simpa only [Category.assoc, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id] using h

/-- 厳密 dg 前合成は全パラメータを保った全次数自然変換を与える。 -/
def dgFunctorParamPre {K : Complex A} {M N : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K M N) :
    DGFunctorParamTrans A B E K (H.comp M) (H.comp N) where
  app x := τ.app (H.obj x)
  naturality := dgFunctorParamPre_naturality A D E B H τ

/-- 全次数自然変換の end に対する厳密 dg 前合成の chain map。 -/
def dgFunctorHomPre (M N : DGFunctor A D E) :
    dgFunctorHom A D E M N ⟶ dgFunctorHom A B E (H.comp M) (H.comp N) :=
  (dgFunctorHomEquiv A B E _ _ _).symm
    (dgFunctorParamPre A D E B H ((dgFunctorHomEquiv A D E _ M N) (𝟙 _)))

/-- 前合成の全対象評価は、元の同じ対象像での評価そのもの。 -/
@[reassoc (attr := simp)]
lemma dgFunctorHomPre_π (M N : DGFunctor A D E) (x : B) :
    dgFunctorHomPre A D E B H M N ≫ dgFunctorHomπ A B E (H.comp M) (H.comp N) x =
      dgFunctorHomπ A D E M N (H.obj x) := by
  rw [dgFunctorHomPre, dgFunctorHomEquiv_symm_π]
  change 𝟙 _ ≫ dgFunctorHomπ A D E M N (H.obj x) = _
  exact Category.id_comp _

end SerrePositivity.KST.SConstruction
