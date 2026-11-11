module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingNullPerfectEquivalence
public import SerrePositivity.KST.SConstruction.PerfectStableArrowSquareComparison

/-!
概要：元恒等対角と V 包含の Cat^perf 区間全体を指定二頂点付きで比較する。
方針：元 S の厳密因子化を同じ固定 ν の合成則に渡す。
規約：V 始域の成分は同じ元対角因子化辺、終域の成分は恒等辺。
使われ方：実右零化面の包含側の全比較と四辺 prism の共有頂点。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [DGCategory R C] [Small.{u} C]
local notation "A" => dgIdentityHomGluingBaseInput R C
local notation "B" => dgIdentityHomGluingGluingInput R C
local notation "V" => dgIdentityHomGluingNullInput R C
local notation "f" => dgIdentityHomGluingDiagonalInputMap R C
local notation "g" => dgIdentityHomGluingNullInputMap R C
local notation "a" => dgIdentityHomGluingDiagonalNullFactorInputMap R C
local notation "ν" => dgKInputNuMap R
local notation "hA" => dgKInputStableValue_isIdempotentComplete R (A)
local notation "hB" => dgKInputStableValue_isIdempotentComplete R (B)
local notation "hV" => dgKInputStableValue_isIdempotentComplete R (V)

/-- 概要：元 S の対角因子化の合成は元恒等対角辺を厳密に回収する。
方針：同じ元 factor の一般回収式を元恒等 cone 収縮に適用する。
規約：新しい対角を選ばない。使われ方：指定包含辺の全可換式。 -/
lemma dgIdentityHomGluingDiagonalNullFactorInputMap_inclusion : (a) ≫ (g) = (f) :=
  dgIdentityHomGluingNullFactorInputMap_comp R C (dgIdentityHomGluingDiagonal R C)
    (fun x => ⟨dgIdentityHomGluingContractingElement R C x,
      dgIdentityHomGluingContractingElement_d R C x⟩)

/-- 概要：同じ実対角因子化は固定 ν の完全射の合成でも元対角を回収する。
方針：元ラベル付き Perf 関手の合成則と固定 ν 辺回収を使う。
規約：完全射の厳密等号。使われ方：全区間比較の指定二成分可換式。 -/
lemma dgIdentityHomGluingDiagonalNullFactorNu_inclusion :
    (ν (a)).hom ≫ (ν (g)).hom = (ν (f)).hom := by
  rw [dgKInputNuMap_eq, dgKInputNuMap_eq, dgKInputNuMap_eq]
  exact (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.hom
    ((presentedPerfectDGStableCategoryFunctor R).map_comp (a) (g))).symm.trans
      (congrArg (fun e => (presentedPerfectDGExactMap R e).hom)
        (dgIdentityHomGluingDiagonalNullFactorInputMap_inclusion R C))

/-- 概要：元対角区間と実 V 包含区間を同じ始域成分・恒等終域成分で比較する。
方針：固定 ν の厳密合成式を元二成分付き区間比較へ渡す。
規約：両端点経路を保持。使われ方：実右面の包含側 prism。 -/
def dgIdentityHomGluingNullDiagonalArrowWitness : PerfectStableArrowSquareWitness
    (ν (f)) (ν (g)) (ν (a)) (𝟙 (dgKInputStableValue R (B))) (hA) (hB) (hV) (hB) := by
  apply perfectStableArrowSquareWitness
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (ν (f)).hom (ν (f)).hom :=
    Iso.refl (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((ν (f)).hom)))
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e (Category.comp_id (ν (f)).hom).symm
    (dgIdentityHomGluingDiagonalNullFactorNu_inclusion R C).symm

/-- 概要：元対角の包含側区間全体と実 V 包含側区間全体は指定同型を持つ。
方針：元始域因子化の ν 同値性と恒等終域成分を同じ区間証人へ代入する。
規約：元全ホモトピーと指定両成分を保持。使われ方：実右面の指定包含全比較。 -/
def dgIdentityHomGluingNullDiagonalArrowComparison [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.yonedaEquiv.symm (perfectStableArrow (ν (f)) (hA) (hB)).edge)
      (SSet.yonedaEquiv.symm (perfectStableArrow (ν (g)) (hV) (hB)).edge) :=
  (dgIdentityHomGluingNullDiagonalArrowWitness R C).comparisonOfEquivalences
    (dgIdentityHomGluingDiagonalNullFactorInputMap_nu_equivalence R C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl (dgKInputStableValue R (B)).obj).isQCatEquivalence

end SerrePositivity.KST.SConstruction
