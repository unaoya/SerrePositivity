module
public import SerrePositivity.InfinityCategories.Derived.DGClosedPinchedRepresentable

/-! # dg 関手による反変実 pinched Hom 関手の自然変換

概要：全 Hom の dg 関手像を、閉零始域に関する実 pinched 図式の自然変換にする。
方針：閉前合成の Hom 鎖写像の自然性と、実 pinched 鎖写像の合成則を使う。
規約：対象の閉零包装を明示する。使われ方：元の屋根図式と商内の屋根図式の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]
variable [Small.{u} D] [Small.{u} E] (F : DGFunctor A D E)

/-- dg 関手の全 Hom 写像から得る、閉零圏上の実 pinched 図式の自然変換。 -/
def dgClosedPinchedFunctorMap (y : D) : dgClosedPinchedRepresentable A D y ⟶
    F.onClosed.op ⋙ dgClosedPinchedRepresentable A E (F.obj y) where
  app q := pinchedHomChainMap (F.map (ForgetEnrichment.to (Complex A) q.unop) y)
  naturality {q p} r := by
    change pinchedHomChainMap (dgClosedPrecomposition A D
      (q := ForgetEnrichment.to (Complex A) p.unop)
      (x := ForgetEnrichment.to (Complex A) q.unop) (y := y) r.unop) ≫
        pinchedHomChainMap (F.map (ForgetEnrichment.to (Complex A) p.unop) y) = _
    exact (pinchedHomChainMap_comp _ _).symm.trans
      ((congrArg pinchedHomChainMap (dgClosedPrecomposition_naturality A D E F
        (p := ForgetEnrichment.to (Complex A) p.unop)
        (q := ForgetEnrichment.to (Complex A) q.unop) (y := y) r.unop)).trans
          (pinchedHomChainMap_comp _ _))

/-- 比較自然変換の各成分は、元の指定 Hom 鎖写像による実 pinched 写像。 -/
lemma dgClosedPinchedFunctorMap_app (y : D) (q : (ClosedCategory A D)ᵒᵖ) :
    (dgClosedPinchedFunctorMap A D E F y).app q =
      pinchedHomChainMap (F.map (ForgetEnrichment.to (Complex A) q.unop) y) := rfl

end SerrePositivity.InfinityCategories
