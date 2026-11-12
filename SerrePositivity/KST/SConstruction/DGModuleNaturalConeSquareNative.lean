module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeSquare
public import SerrePositivity.KST.SConstruction.DGModuleKStrictNatTransNative
public import SerrePositivity.KST.SConstruction.DGModuleConeHomotopyTriangle

/-!
概要：指定元可換 square の cone 全比較を native 全関手同型へ束ねる。
方針：元二縦辺の K(D) 同値を同じ元実 cone 射へ反映する。
規約：元全厳密比較・元零ホモトピーを保持する。
使われ方：元小模型の評価同型を保つ gluing cone の全図式比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
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

/-- 概要：元二縦辺が K(D) 同値なら同じ cone square 閉成分も K(D) 同値。
方針：同じ元 cone 射の三角形判定を使う。
規約：元零ホモトピー保持。使われ方：全 native 比較の可逆性。 -/
lemma dgModuleNaturalConeSquare_isIso (x : P) :
    IsIso ((moduleToHomotopy R D).map
      (dgModuleNaturalConeArrow R D (CA) (CB) (θ) x)) := by
  rw [dgModuleNaturalConeSquare_arrow]
  exact dgModuleConeMapOfHomotopy_isIso R D (f x) (g x) (a x) (b x)
    (dgModuleNaturalConeSquareHomotopy R D F G F' G' α β l r hsq x) (ha x) (hb x)

/-- 概要：元四辺を保つ cone square の native 全関手同型。
方針：元全厳密比較と同じ元実 cone 射の K(D) 同値を束ねる。
規約：同じ全ホモトピーを保持。
使われ方：元評価同型を保つ実 gluing cone の全比較。 -/
def dgModuleNaturalConeSquareNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CA)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CB)) :=
  dgModuleFunctorIsoOfKStrictNatTrans R D (CA) (CB) (θ)
    (dgModuleNaturalConeSquare_isIso R D F G F' G' α β l r hsq ha hb)
end SerrePositivity.KST.SConstruction
