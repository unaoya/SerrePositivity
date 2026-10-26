module
public import SerrePositivity.DifferentialGraded.Quotient.ParameterExtension
public import SerrePositivity.DifferentialGraded.Quotient.Universal

/-!
概要：同じ選択収縮の後合成族について、全パラメータの商延長を実構成する。
方針：後合成側の元の全次数自然性を選択収縮そのものに適用する。
規約：この経路の ε 整合を追加入力に残さず、選んだ収縮を変更しない。
使われ方：D-8 e の同じ実商・零角辺の全 native Hom 作用の後合成部品。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex
variable (R : Type u) [CommRing R] {D : Type v} [DGCategory R D]
  {E : Type w} [DGCategory R E] {T : Type z} [DGCategory R T]

/-- 元の dg 関手による全パラメータ変換の厳密な前合成。 -/
def parameterPrecomposition (F : DGFunctor R D E) {K : Complex R}
    {H H' : DGFunctor R E T}
    (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) H H') :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj K) (F.comp H) (F.comp H') where
  app x := τ.app (F.obj x)
  naturality x y := by
    apply (gradedFamilyNaturality_iff_homogeneous R (F.comp H) (F.comp H')
      (fun x => τ.app (F.obj x)) x y).2
    intro k p t f
    exact (gradedFamilyNaturality_iff_homogeneous R H H' τ.app (F.obj x) (F.obj y)).1
      (τ.naturality (F.obj x) (F.obj y)) k p t ((F.map x y).f p f)

private lemma parameterTrans_hext {K : Complex R} {F F' G G' : DGFunctor R D T}
    (hF : F = F') (hG : G = G')
    (a : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) F G)
    (b : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) F' G')
    (h : HEq a.app b.app) : HEq a b := by
  cases hF
  cases hG
  apply heq_of_eq
  exact GradedNatTrans.ext (eq_of_heq h)

variable [Small.{u} D] {S : Set D} (C : ContractedFunctor R D S E)
  {K : Complex R} {H H' : DGFunctor R E T}
  (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) H H')

/-- 同じ選択収縮への自然性から ε 整合を実証した全パラメータ延長。 -/
def parameterExtension_postcomposition :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj K)
      (extension R (C.postcomp R H)) (extension R (C.postcomp R H')) :=
  parameterExtension R (C.postcomp R H) (C.postcomp R H')
    (parameterPrecomposition R C.toDGFunctor τ) (fun b k t =>
      (gradedFamilyNaturality_iff_homogeneous R H H' τ.app
        (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val)).1
          (τ.naturality _ _) k (-1) t (C.homotopy b))

lemma parameterExtension_postcomposition_app (x : QuotientObject D S) :
    (parameterExtension_postcomposition R C τ).app x = τ.app (C.toDGFunctor.obj x.val) := rfl

/-- 元の厳密な商延長の後合成等号のもとで、全パラメータ変換も同じ前合成作用。 -/
theorem parameterExtension_postcomposition_heq :
    HEq (parameterExtension_postcomposition R C τ)
      (parameterPrecomposition R (extension R C) τ) := by
  exact parameterTrans_hext R (extension_postcomp R C H) (extension_postcomp R C H')
    (parameterExtension_postcomposition R C τ) (parameterPrecomposition R (extension R C) τ) HEq.rfl

end SerrePositivity.DifferentialGraded.DGQuotient
