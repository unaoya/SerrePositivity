module
public import SerrePositivity.KST.SConstruction.DGFunctorHomUniversal

/-! # dg 関手の Hom end 上の厳密な後合成作用
概要：標的への厳密 dg 関手は、元の全次数自然変換とその全パラメータへ作用する。
方針：元の Hom chain map で全対象の評価を写し、合成保存で全次数自然性を移す。
規約：元のパラメータを変更しない。使われ方：dg 入力の非離散 Hom と K の豊穣化。
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
  (E : Type w) [DGCategory A E] (B : Type t) [DGCategory A B]
  (H : DGFunctor A E B)

omit [Small.{u} D] in
/-- 全次数自然性を元の Hom chain map で後合成した可換式。 -/
lemma dgFunctorParamPost_naturality {K : Complex A} {M N : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K M N) (x y : D) :
    (β_ K (x ⟶[Complex A] y)).hom ≫
      ((M.map x y ≫ H.map (M.obj x) (M.obj y)) ⊗ₘ
        (τ.app y ≫ H.map (M.obj y) (N.obj y))) ≫
        eComp (Complex A) (H.obj (M.obj x)) (H.obj (M.obj y)) (H.obj (N.obj y)) =
    ((τ.app x ≫ H.map (M.obj x) (N.obj x)) ⊗ₘ
      (N.map x y ≫ H.map (N.obj x) (N.obj y))) ≫
        eComp (Complex A) (H.obj (M.obj x)) (H.obj (N.obj x)) (H.obj (N.obj y)) := by
  have h₀ : (β_ K (x ⟶[Complex A] y)).hom ≫ (M.map x y ⊗ₘ τ.app y) ≫
      eComp (Complex A) (M.obj x) (M.obj y) (N.obj y) =
    (τ.app x ⊗ₘ N.map x y) ≫ eComp (Complex A) (M.obj x) (N.obj x) (N.obj y) :=
    τ.naturality x y
  have h := congrArg (fun k => k ≫ H.map (M.obj x) (N.obj y)) h₀
  simpa only [Category.assoc, EnrichedFunctor.map_comp,
    tensorHom_comp_tensorHom_assoc] using h

/-- 厳密 dg 後合成は、全パラメータを保った全次数自然変換を与える。 -/
def dgFunctorParamPost {K : Complex A} {M N : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K M N) :
    DGFunctorParamTrans A D B K (M.comp H) (N.comp H) where
  app x := τ.app x ≫ H.map (M.obj x) (N.obj x)
  naturality := dgFunctorParamPost_naturality A D E B H τ

/-- 元の全次数自然変換の end に対する、厳密 dg 後合成の chain map。 -/
def dgFunctorHomPost (M N : DGFunctor A D E) :
    dgFunctorHom A D E M N ⟶ dgFunctorHom A D B (M.comp H) (N.comp H) :=
  (dgFunctorHomEquiv A D B _ _ _).symm
    (dgFunctorParamPost A D E B H ((dgFunctorHomEquiv A D E _ M N) (𝟙 _)))

/-- 後合成の全対象評価は元の同じ Hom chain map そのもの。 -/
@[reassoc (attr := simp)]
lemma dgFunctorHomPost_π (M N : DGFunctor A D E) (x : D) :
    dgFunctorHomPost A D E B H M N ≫ dgFunctorHomπ A D B (M.comp H) (N.comp H) x =
      dgFunctorHomπ A D E M N x ≫ H.map (M.obj x) (N.obj x) := by
  rw [dgFunctorHomPost, dgFunctorHomEquiv_symm_π]
  change (𝟙 _ ≫ dgFunctorHomπ A D E M N x) ≫ H.map (M.obj x) (N.obj x) = _
  rw [Category.id_comp]

end SerrePositivity.KST.SConstruction
