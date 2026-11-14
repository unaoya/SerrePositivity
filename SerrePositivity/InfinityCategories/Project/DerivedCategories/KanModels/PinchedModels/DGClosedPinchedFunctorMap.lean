module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGClosedPinchedRepresentable

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded
variable (A : Type u) [CommRing A] (D E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
variable [Small.{u} D] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

/-- dg 関手の全 Hom 写像から得る、閉零圏上の実 pinched 図式の自然変換。 -/
def dgClosedPinchedFunctorMap (y : D) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPinchedRepresentable A D y ⟶
    F.onClosed.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPinchedRepresentable A E (F.obj y) where
  app q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (F.map (ForgetEnrichment.to (Complex A) q.unop) y)
  naturality {q p} r := by
    change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D
      (q := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) p.unop)
      (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) q.unop) (y := y) r.unop) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (F.map (ForgetEnrichment.to (Complex A) p.unop) y) = _
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp _ _).symm.trans
      ((congrArg _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_naturality A D E F
        (p := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) p.unop)
        (q := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) q.unop) (y := y) r.unop)).trans
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp _ _))

/-- 比較自然変換の各成分は、元の指定 Hom 鎖写像による実 pinched 写像。 -/
lemma dgClosedPinchedFunctorMap_app (y : D) (q : (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A D)ᵒᵖ) :
    (dgClosedPinchedFunctorMap A D E F y).app q =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (F.map (ForgetEnrichment.to (Complex A) q.unop) y) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
