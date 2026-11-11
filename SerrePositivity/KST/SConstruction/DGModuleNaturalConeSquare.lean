module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeSquareInput
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeDesc
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConnectingConeComparison

/-!
概要：指定全厳密可換 square を同じ元 cone の全比較へ拡張する。
方針：既存前合成零化入力を元右包含後の終辺と同じ descent に渡す。
規約：元四辺・零ホモトピー・全次数を保持する。
使われ方：元小模型の Yoneda 評価を保つ実 gluing cone の全図式比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P]
  (F G F' G' : DGFunctor R P (RightModule R D))
  (α : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (β : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F' G')
  (l : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F F') (r : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G G')
  (hsq : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp α r = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp l β)
include hsq
local notation "f" => dgModuleNaturalConeArrow R D F G α
local notation "g" => dgModuleNaturalConeArrow R D F' G' β
local notation "a" => dgModuleNaturalConeArrow R D F F' l
local notation "b" => dgModuleNaturalConeArrow R D G G' r


local notation "CA" => dgModuleNaturalConeFunctor R D F G α
local notation "CB" => dgModuleNaturalConeFunctor R D F' G' β
local notation "ι" => dgModuleNaturalConeInr R D F' G' β
local notation "ξ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp r (ι)
local notation "s" => dgModuleNaturalConePrecompositionInput R D F F' G' l β

/-- 概要：同じ全厳密 square の cone 入力微分は指定右包含後の終辺。
方針：元零ホモトピー square の境界式へ同じ全閉成分を渡す。
規約：元指定四辺を保持。使われ方：実 cone descent の微分入力。 -/
lemma dgModuleNaturalConeSquare_boundary (x : P) :
    (moduleHom R D (F.obj x) ((CB).obj x)).d (-1) 0 (s x) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (f x ≫ dgModuleNaturalConeArrow R D G (CB) (ξ) x))).val := by
  rw [dgModuleNaturalConeSquareInput_recovery R D F G F' G' α β l r hsq]
  exact (moduleConeHomotopyInput_d R D (f x) (g x) (a x) (b x)
    (dgModuleNaturalConeSquareHomotopy R D F G F' G' α β l r hsq x)).trans
      (congrArg (fun t => (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (f x ≫ t))).val)
        ((congrArg (fun t => b x ≫ t) (dgModuleNaturalConeInr_arrow R D F' G' β x).symm).trans
          (dgModuleNaturalConeArrow_comp R D G G' (CB) r (ι) x).symm))

/-- 概要：元可換 square を保つ同じ元二 cone の全厳密比較。
方針：同じ全自然な入力を元実 descent へ渡す。
規約：元比較を成分だけの存在で代用しない。
使われ方：元小模型の指定評価同型を保つ cone 全比較。 -/
def dgModuleNaturalConeSquare : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (CA) (CB) :=
  dgModuleNaturalConeDesc R D F G (CB) α (ξ) (s)
    (dgModuleNaturalConeSquare_boundary R D F G F' G' α β l r hsq)
    (dgModuleNaturalConePrecompositionInput_naturality R D F F' G' l β)

/-- 概要：元全 cone square 比較の閉成分は同じ実 square の cone 射。
方針：元入力回収と元右包含後の終辺の回収を合わせる。
規約：同じ元零ホモトピーを保持。使われ方：native 可逆性と指定境界の認証。 -/
lemma dgModuleNaturalConeSquare_arrow (x : P) :
    dgModuleNaturalConeArrow R D (CA) (CB)
      (dgModuleNaturalConeSquare R D F G F' G' α β l r hsq) x =
      moduleConeMapOfHomotopy R D (f x) (g x) (a x) (b x)
        (dgModuleNaturalConeSquareHomotopy R D F G F' G' α β l r hsq x) := by
  exact (dgModuleNaturalConeDesc_arrow R D F G (CB) α (ξ) (s)
    (dgModuleNaturalConeSquare_boundary R D F G F' G' α β l r hsq)
    (dgModuleNaturalConePrecompositionInput_naturality R D F F' G' l β) x).trans
    (dgModuleConeDesc_recovery R D (f x) (g x) (a x) (b x)
      (dgModuleNaturalConeSquareHomotopy R D F G F' G' α β l r hsq x)
      (s x) (dgModuleNaturalConeArrow R D G (CB) (ξ) x)
      (dgModuleNaturalConeSquare_boundary R D F G F' G' α β l r hsq x)
      (dgModuleNaturalConeSquareInput_recovery R D F G F' G' α β l r hsq x)
      ((dgModuleNaturalConeArrow_comp R D G G' (CB) r (ι) x).trans
        (congrArg (fun t => b x ≫ t) (dgModuleNaturalConeInr_arrow R D F' G' β x))))
end SerrePositivity.KST.SConstruction
