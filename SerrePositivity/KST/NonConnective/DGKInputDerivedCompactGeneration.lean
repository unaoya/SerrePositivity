module
public import SerrePositivity.DifferentialGraded.Morita.CriterionDerivedEquivalence
public import SerrePositivity.DifferentialGraded.Perfect.SmallEnhancement

/-!
概要：同じ実 dg 入力の主導来圏を、小 Perf 代表の実像で compact 生成する。
方針：小 Perf 評価の同値と元の主導来局所生成を使う。
規約：生成族を新しい入力仮定にせず、元の包含射を保持する。
使われ方：K-7 d4・e の主導来 Morita 判定に共通の生成証拠。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R]

/-- 小 Perf 代表の元の主導来圏への実像。 -/
def dgKInputDerivedCompactFamily (C : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
    (x : SmallPerfectDGModuleOver R C Set.univ) : DerivedModuleCategory R C :=
  (perfectModuleInclusion R C Set.univ).obj ((smallPerfectDGModuleToPerfect R C Set.univ).obj
    ((toHomotopy R (SmallPerfectDGModuleOver R C Set.univ)).obj (ForgetEnrichment.of (Complex R) x)))

/-- 同じ実像は追加仮定なしで主導来圏を compact 生成する。 -/
theorem dgKInputDerivedCompactGeneration (C : Type (max (u + 1) v))
    [DGCategory R C] [Small.{u} C] :
    Morita.CriterionDerivedCompactGeneration R C (dgKInputDerivedCompactFamily R C) where
  compact x := (moduleCompact_iff_perfect R C _).mpr
    ((smallPerfectDGModuleToPerfect R C Set.univ).obj
      ((toHomotopy R (SmallPerfectDGModuleOver R C Set.univ)).obj
        (ForgetEnrichment.of (Complex R) x))).property
  localizing Q htri hiso hcop hgen X := by
    letI := htri
    letI := hiso
    have hperf : ∀ Y : DerivedModuleCategory R C, modulePerfect R C Y → Q Y := by
      intro Y hY
      obtain ⟨c, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (smallPerfectDGModuleToPerfect R C Set.univ)
        (⟨Y, hY⟩ : PerfectModuleCategoryOver R C Set.univ)
      exact Q.prop_of_iso ((perfectModuleInclusion R C Set.univ).mapIso e)
        (hgen (ForgetEnrichment.to (Complex R) c.as))
    exact moduleLocalizing_all R C Q hcop hperf X


end SerrePositivity.KST.NonConnective
