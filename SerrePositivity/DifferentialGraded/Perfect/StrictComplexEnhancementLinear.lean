module
public import SerrePositivity.DifferentialGraded.Perfect.StrictComplexEnhancement

/-! # 既存PerfectHomotopyの全Hom dg表示における線形性と包含の比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 全複体ホモトピー圏への比較は加法的。H⁰包含と複体比較の合成として継承する。 -/
instance strictPerfectDGComplexToHomotopyAdditive :
    (strictPerfectDGComplexToHomotopy A).Additive := by
  dsimp [strictPerfectDGComplexToHomotopy]
  infer_instance

/-- 全複体ホモトピー圏への比較は主Hom由来のA線形性を保つ。 -/
instance strictPerfectDGComplexToHomotopyLinear :
    (strictPerfectDGComplexToHomotopy A).Linear A := by
  dsimp [strictPerfectDGComplexToHomotopy]
  infer_instance

/-- 既存PerfectHomotopyへの制限は加法性を保つ。 -/
instance strictPerfectDGComplexToPerfectAdditive :
    (strictPerfectDGComplexToPerfect A).Additive := by
  dsimp [strictPerfectDGComplexToPerfect]
  infer_instance

/-- 既存PerfectHomotopyへの比較はA線形。既存の充満部分圏の射の外延性を使う。 -/
instance strictPerfectDGComplexToPerfectLinear : (strictPerfectDGComplexToPerfect A).Linear A where
  map_smul f a := (perfectHomotopyProperty A).hom_ext
    ((strictPerfectDGComplexToHomotopy A).map_smul a f)

/-- 選択したH⁰同値の順関手は加法的で、逆関手にも加法性が移る。 -/
instance strictPerfectDGComplexHomotopyEquivalenceFunctorAdditive :
    (strictPerfectDGComplexHomotopyEquivalence A).functor.Additive :=
  strictPerfectDGComplexToPerfectAdditive A

/-- 選択したH⁰同値の順関手はA線形で、逆関手にも線形性が移る。 -/
instance strictPerfectDGComplexHomotopyEquivalenceFunctorLinear :
    (strictPerfectDGComplexHomotopyEquivalence A).functor.Linear A :=
  strictPerfectDGComplexToPerfectLinear A

/-- 既存perfect包含を経由する比較は、元の全複体ホモトピー圏への比較と自然同型で一致する。 -/
def strictPerfectDGComplexToPerfectCompInclusion :
    strictPerfectDGComplexToPerfect A ⋙ perfectHomotopyInclusion A ≅
      strictPerfectDGComplexToHomotopy A :=
  (perfectHomotopyProperty A).liftCompιIso _ _

end SerrePositivity.DifferentialGraded
