module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeBoundary
public import SerrePositivity.KST.SConstruction.DGPerfectModuleUnderlying
public import SerrePositivity.KST.SConstruction.DGHomGluingInverseRotationCone

/-!
概要：元 Hom gluing の逆回転射の実 cone を、同じ全 Hom を持つ dg 関手へ束ねる。
方針：構成済みの全 Hom 自然性を厳密自然変換と実 cone 構成へ渡す。
規約：同じ逆回転射と実 cone を回収する。比較成分の自然性は別途必要。
使われ方：保存済みの逆回転 cone 比較を全関手比較へ拡張する始域。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)
local notation "F" => dgPerfectModuleUnderlying R E (dgHomGluingLoopConeFunctor R C D E p q)
local notation "G" => dgPerfectModuleUnderlying R E (dgHomGluingDoubleShiftLeftFunctor R C D E p q)

/-- 概要：元実逆回転射を束ねた全次数厳密自然変換。
方針：同じ元射の全 Hom 自然性を使う。
規約：元加群射を保持。使われ方：実逆回転 cone 関手の入力。 -/
def dgHomGluingInverseRotationStrictNatTrans : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (F) (G) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R E
    (dgHomGluingInverseRotationModuleMap R C D E p q)
    (dgHomGluingInverseRotation_module_naturality R C D E p q)

/-- 概要：厳密比較の元閉射は保存済みの実逆回転射と一致する。
方針：同じ閉射・閉元対応の逆律を適用する。
規約：対象別の射の選択なし。使われ方：同じ実 cone の照合。 -/
lemma dgHomGluingInverseRotationStrictNatTrans_arrow (X : L) :
    dgModuleNaturalConeArrow R E (F) (G)
      (dgHomGluingInverseRotationStrictNatTrans R C D E p q) X =
        dgHomGluingInverseRotationModuleMap R C D E p q X := by
  change (closedHomEquiv R (RightModule R E) _ _).symm
    ((closedHomEquiv R (RightModule R E) _ _)
      (dgHomGluingInverseRotationModuleMap R C D E p q X)) = _
  exact (closedHomEquiv R (RightModule R E) _ _).symm_apply_apply _

/-- 概要：同じ元実逆回転 cone の全 dg 関手。
方針：元の厳密比較へ全 Hom の cone 構成を適用する。
規約：比較成分の自然性を先取りしない。使われ方：実商合成の全比較の始域。 -/
def dgHomGluingInverseRotationConeFamily : DGFunctor R (L) (RightModule R E) :=
  dgModuleNaturalConeFunctor R E (F) (G)
    (dgHomGluingInverseRotationStrictNatTrans R C D E p q)

/-- 概要：全 dg 関手の対象は元の実逆回転射の同じ cone。
方針：元閉射の回収等号を同じ cone 構成に適用する。
規約：実 cone を選び直さない。使われ方：保存済み比較成分の始域照合。 -/
lemma dgHomGluingInverseRotationConeFamily_obj (X : L) :
    ForgetEnrichment.of (Complex R)
      ((dgHomGluingInverseRotationConeFamily R C D E p q).obj X) =
        moduleCone R E (dgHomGluingInverseRotationModuleMap R C D E p q X) :=
  congrArg (fun a => moduleCone R E a)
    (dgHomGluingInverseRotationStrictNatTrans_arrow R C D E p q X)

/-- 概要：実逆回転 cone への同じ標準右包含の全次数自然変換。
方針：元逆回転比較の実 cone 関手に標準包含を適用する。
規約：元の二重 shift 側を始域として保持。
使われ方：指定上二単体の包含境界を全関手族として保持する。 -/
def dgHomGluingInverseRotationConeFamilyInr : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (G)
    (dgHomGluingInverseRotationConeFamily R C D E p q) :=
  dgModuleNaturalConeInr R E (F) (G)
    (dgHomGluingInverseRotationStrictNatTrans R C D E p q)
end SerrePositivity.KST.SConstruction
