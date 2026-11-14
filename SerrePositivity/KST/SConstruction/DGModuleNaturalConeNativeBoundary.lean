module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeImageNative
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeImageBoundary
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeSquareNative
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeSquareBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGStrictNatTransNerveHom

/-!
概要：元 cone image・評価 square の native 全比較が元包含を同じ射として保つ。
方針：元全厳密包含等号を同じ native 順射と合成則へ写す。
規約：元比較・元包含を別の代表に置き換えない。
使われ方：元実逆回転の上指定二単体を二段 realization へ接続する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
section Image
variable (R : Type u) [CommRing R]
  (E : Type v) [DGCategory R E] [Small.{u} E]
  (D : Type (max (u + 1) v)) [DGCategory R D] [Small.{u} D]
  {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
  (Q : DGFunctor R (RightModule R D) (RightModule R E))
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "FQ" => DGFunctor.comp F Q
local notation "GQ" => DGFunctor.comp G Q
local notation "CQ" => DGFunctor.comp (CF) Q
local notation "ηQ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η Q
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "νQ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (ν) Q
local notation "a" => dgModuleNaturalConeArrow R D F G η
local notation "s" => dgModuleNaturalConeImageInput R E D F G η Q


local notation "CηQ" => dgModuleNaturalConeFunctor R E (FQ) (GQ) (ηQ)
local notation "θ" => dgModuleNaturalConeImage R E D F G η Q

/-- 概要：元 cone image の native 順射は同じ元全厳密比較の射。
方針：元全ホモトピーの定義を回収する。
規約：同じ辺の類。使われ方：元包含の全比較への接続。 -/
lemma dgModuleNaturalConeImageNerveComparison_hom :
    (dgModuleNaturalConeImageNerveComparison R E D F G η Q).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E) (θ) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_spec R P (RightModule R E) (θ)).symm

/-- 概要：元 native cone image 全比較は右包含の同じ実像を回収する。
方針：同じ元包含の厳密合成等号を native 合成則で運ぶ。
規約：元包含の像を保持。使われ方：元上二単体の実評価境界。 -/
lemma dgModuleNaturalConeImageNerveComparison_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E)
        (dgModuleNaturalConeInr R E (FQ) (GQ) (ηQ)) ≫
      (dgModuleNaturalConeImageNerveComparison R E D F G η Q).hom =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E) (νQ) := by
  rw [dgModuleNaturalConeImageNerveComparison_hom]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_comp R P (RightModule R E)
    (dgModuleNaturalConeInr R E (FQ) (GQ) (ηQ)) (θ)).symm.trans
      (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E) t)
        (dgModuleNaturalConeImage_inr R E D F G η Q))

/-- 概要：元 cone image 全比較の逆は元包含像を元の像 cone 包含へ戻す。
方針：同じ順方向包含等号に同じ逆射を後合成する。
規約：別の逆を選ばない。使われ方：元実評価全比較の第一因子。 -/
lemma dgModuleNaturalConeImageNerveComparison_inr_inv :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E) (νQ) ≫
      (dgModuleNaturalConeImageNerveComparison R E D F G η Q).inv =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E)
          (dgModuleNaturalConeInr R E (FQ) (GQ) (ηQ)) := by
  rw [← dgModuleNaturalConeImageNerveComparison_inr R E D F G η Q,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]
end Image
section Square
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type (max (u + 1) v)} [DGCategory R P]
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


local notation "θ" => dgModuleNaturalConeSquare R D F G F' G' α β l r hsq
variable (ha : ∀ x : P, IsIso ((moduleToHomotopy R D).map
    (dgModuleNaturalConeArrow R D F F' l x)))
  (hb : ∀ x : P, IsIso ((moduleToHomotopy R D).map
    (dgModuleNaturalConeArrow R D G G' r x)))
include ha hb

/-- 概要：元 cone square の native 順射は同じ元全厳密比較の射。
方針：元全ホモトピーの定義を回収する。
規約：元比較の同じ順射。使われ方：元評価 square の包含境界。 -/
lemma dgModuleNaturalConeSquareNerveComparison_hom :
    (dgModuleNaturalConeSquareNerveComparison R D F G F' G' α β l r hsq ha hb).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R D) (θ) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_spec R P (RightModule R D) (θ)).symm

/-- 概要：元 native cone square の包含制限は元右軸と同じ終域包含の全合成。
方針：元全厳密包含等号と native 合成則を使用する。
規約：指定右軸・包含を保持。使われ方：元実 realization の上二単体境界。 -/
lemma dgModuleNaturalConeSquareNerveComparison_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R D) (dgModuleNaturalConeInr R D F G α) ≫
      (dgModuleNaturalConeSquareNerveComparison R D F G F' G' α β l r hsq ha hb).hom =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R D) r ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R D) (ι) := by
  rw [dgModuleNaturalConeSquareNerveComparison_hom]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_comp R P (RightModule R D)
    (dgModuleNaturalConeInr R D F G α) (θ)).symm.trans
      ((congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R D) t)
        (dgModuleNaturalConeSquare_inr R D F G F' G' α β l r hsq)).trans
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_comp R P (RightModule R D) r (ι)))
end Square
end SerrePositivity.KST.SConstruction
