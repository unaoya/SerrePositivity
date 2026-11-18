module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveConstantHom
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DerivedNatTransComponent
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.OrdinaryDerivedConstant
/-!
概要：元の定値複体自然変換を、同じ導来成分射の定値二胞体へ回収する。
方針：元の全円柱の Arrow 比較を、既存の定値端点同型で輸送する。
規約：同じ通常射・同じ導来源・元の全添字圏を保持する。
使われ方：自由単位の全屋根三角形を標準単位の族公式に接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (I : Type (u + 1)) [Category.{u} I]

/-- 概要：定値自然変換の元の導来二胞体は、同じ成分射の導来像の定値族。
方針：全円柱の比較と既存の両端同型を相殺する。
規約：各点上の一致に縮めない。使われ方：実単位・標的 augmentation の全族計算。 -/
lemma complexOrdinaryDerivedNatTransHom_const {X Y : Complex A} (f : X ⟶ Y) :
    (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstantIso A I X).inv ≫
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A ((Functor.const I).map f) ≫
        (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstantIso A I Y).hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap (nerve I) (Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk f).map (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated) := by
  have h : Arrow.mk (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A ((Functor.const I).map f)) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap (nerve I) (Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk f).map (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated)) :=
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.mixedNerve_const_postcomp_arrow f (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)
  obtain ⟨hx, hy, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  rw [h]
  simp [_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstantIso, Category.assoc]

end SerrePositivity.ComplexLimits
