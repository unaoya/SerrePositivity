module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConePrecompositionInput
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConnectingConeComparison
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationInv

/-!
概要：指定した全厳密合成から後の射への cone 全比較を構成する。
方針：指定前合成零化入力を同じ実 cone descent に渡す。
規約：元三辺の閉射と零ホモトピーを保持する。
使われ方：元入力同型を保つ connecting cone と実逆回転の全比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P]
  (F G H : DGFunctor R P (RightModule R D))
  (α : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (β : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H)
local notation "γ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp α β
local notation "CB" => dgModuleNaturalConeFunctor R D G H β
local notation "CC" => dgModuleNaturalConeFunctor R D F H (γ)
local notation "ι" => dgModuleNaturalConeInr R D G H β
local notation "a" => dgModuleNaturalConeArrow R D F G α
local notation "b" => dgModuleNaturalConeArrow R D G H β
local notation "c" => dgModuleNaturalConeArrow R D F H (γ)
local notation "s" => dgModuleNaturalConePrecompositionInput R D F G H α β

/-- 概要：元前合成入力の微分は指定合成の右包含後の閉元。
方針：元零ホモトピー square の境界式を適用する。
規約：同じ元包含を使用。使われ方：全 cone descent の指定微分。 -/
lemma dgModuleNaturalConePrecomposition_boundary (x : P) :
    (moduleHom R D (F.obj x) ((CB).obj x)).d (-1) 0 (s x) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (c x ≫ dgModuleNaturalConeArrow R D H (CB) (ι) x))).val := by
  rw [dgModuleNaturalConePrecompositionInput_recovery]
  exact (moduleConeHomotopyInput_d R D (c x) (b x) (a x) (𝟙 _)
    (dgModuleNaturalConePrecompositionSquareHomotopy R D F G H α β x)).trans
      (congrArg (fun t => (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (c x ≫ t))).val)
        ((Category.id_comp _).trans (dgModuleNaturalConeInr_arrow R D G H β x).symm))

/-- 概要：元合成の cone から後の射の cone への全厳密比較。
方針：全自然な指定入力を同じ実 descent へ渡す。
規約：元入力と閉零成分を保持。使われ方：元 connecting cone の比較。 -/
def dgModuleNaturalConePrecomposition : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (CC) (CB) :=
  dgModuleNaturalConeDesc R D F H (CB) (γ) (ι) (s)
    (dgModuleNaturalConePrecomposition_boundary R D F G H α β)
    (dgModuleNaturalConePrecompositionInput_naturality R D F G H α β)

/-- 概要：全比較の閉成分は元零ホモトピー square の実 cone 射。
方針：descent 成分の回収と同じ入力の回収を適用。
規約：元射の厳密等式。使われ方：元実逆回転射との成分照合。 -/
lemma dgModuleNaturalConePrecomposition_arrow (x : P) :
    dgModuleNaturalConeArrow R D (CC) (CB)
      (dgModuleNaturalConePrecomposition R D F G H α β) x =
      moduleConeMapOfHomotopy R D (c x) (b x) (a x) (𝟙 _)
        (dgModuleNaturalConePrecompositionSquareHomotopy R D F G H α β x) := by
  exact (dgModuleNaturalConeDesc_arrow R D F H (CB) (γ) (ι) (s)
    (dgModuleNaturalConePrecomposition_boundary R D F G H α β)
    (dgModuleNaturalConePrecompositionInput_naturality R D F G H α β) x).trans
    (dgModuleConeDesc_recovery R D (c x) (b x) (a x) (𝟙 _)
      (dgModuleNaturalConePrecompositionSquareHomotopy R D F G H α β x)
      (s x) (dgModuleNaturalConeArrow R D H (CB) (ι) x)
      (dgModuleNaturalConePrecomposition_boundary R D F G H α β x)
      (dgModuleNaturalConePrecompositionInput_recovery R D F G H α β x)
      ((dgModuleNaturalConeInr_arrow R D G H β x).trans (Category.id_comp _).symm))
end SerrePositivity.KST.SConstruction
