module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisLaxCone
public import SerrePositivity.KST.SConstruction.DGOdotMilnorActualRightNuBoundary
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingNullDiagonalBoundary

/-!
概要：共通実長方形の V 始域・中央・終域を同じ絶対恒等 lax 面へ比較する。
方針：元対角因子化の ν 同値を使い、実右軸の元対角比較を V 包含へ反映する。
規約：包含・商比較で同じ中央成分を使い、元二端点を保持する。
使われ方：実右面の全四辺比較と VerdierSquareDiagramIso の指定包含・商境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants

open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "A" => dgIdentityHomGluingNullInput R (U)
local notation "B" => dgOdotMilnorRightAxisInput R d
local notation "D" => dgOdotMilnorRightAxisIdentityDifferenceInput R d
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "Λ" => laxCategory (𝟙 (Q)) (𝟙 (Q))
local notation "hQ" => dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d)
local notation "hΛ" => perfectLaxCategory_isIdempotentComplete (𝟙 (Q)) (𝟙 (Q)) (hQ) (hQ)
local notation "i" => dgIdentityHomGluingNullInputMap R (U)
local notation "q" => dgOdotMilnorRightAxisIdentityDifferenceInputMap R d
local notation "f" => dgIdentityHomGluingDiagonalNullFactorInputMap R (U)
local notation "eL" => dgOdotMilnorRightAxisCompletedGluingEquivalence R d
local notation "eT" => dgOdotMilnorRightAxisDifferenceResolvedValueEquivalence R d

/-- 概要：実 V 始域の ν 値から元 resolved 商値への指定同値。
方針：元対角因子化の同じ ν 辺の指定逆に元二段評価を合成する。
規約：元 V 頂点を保持。使われ方：実右面の共有始域成分。 -/
def dgOdotMilnorActualRightSourceEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (A)).obj (Q).obj :=
  (dgOdotMilnorNullDiagonalNu_isQCatEquivalence R d).choose.symm.trans
    (dgOdotMilnorRightAxisBaseValueEquivalence R d)

/-- 概要：実右面の始域比較は同じ指定同値の完全射。
方針：同じ順方向に同値完全性だけを付ける。
規約：始域成分を選び直さない。使われ方：包含・零左辺の共有経路。 -/
def dgOdotMilnorActualRightSourceMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R (A)) (Q) :=
  ⟨(dgOdotMilnorActualRightSourceEquivalence R d).hom,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (dgOdotMilnorActualRightSourceEquivalence R d).isQCatEquivalence⟩

/-- 概要：実中央頂点の比較は同じ completed gluing 同値の完全射。
方針：元順方向に同値完全性を付ける。
規約：包含と商で同じ射を使用。使われ方：四辺 prism の共有中央成分。 -/
def dgOdotMilnorActualRightMiddleMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R (B)) (Λ) :=
  ⟨(eL).hom, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (eL).isQCatEquivalence⟩

/-- 概要：実差終域の比較は元 cone 評価と二段評価を保つ完全射。
方針：同じ指定終域同値に完全性を付ける。
規約：商と零上辺で同じ射を使用。使われ方：四辺 prism の共有終域成分。 -/
def dgOdotMilnorActualRightTargetMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R (D)) (Q) :=
  ⟨(eT).hom, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (eT).isQCatEquivalence⟩

/-- 概要：元 V 包含辺は同じ指定三頂点の下で絶対恒等対角へ全比較される。
方針：元対角因子化の厳密 ν 合成と実右軸の対角比較を同じ ν 同値で反映する。
規約：元実包含と元 completed 中央同値を保持。使われ方：実右面の包含全比較。 -/
def dgOdotMilnorActualRightInclusionLaxComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgKInputNuMap R (i)).hom ≫ (eL).hom)
    ((dgOdotMilnorActualRightSourceEquivalence R d).hom ≫
      (IdentityLax.exactDiagonal (Q)).hom) := by
  have cancelPrefix {X Y Z W : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
      [Quasicategory W] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) (b : X ⟶ Z) (c : Z ⟶ W) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.hom ≫ (e.inv ≫ b) ≫ c) (b ≫ c) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc, Category.id_comp] using
      e.homInvIso.postcomp (b ≫ c)
  let eF := (dgOdotMilnorNullDiagonalNu_isQCatEquivalence R d).choose
  let eB := (dgOdotMilnorRightAxisBaseValueEquivalence R d).hom
  let diag := (IdentityLax.exactDiagonal (Q)).hom
  have hi := @dgIdentityHomGluingDiagonalNullFactorNu_inclusion R _ (U) _ _
  have hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (eF.hom ≫ (dgKInputNuMap R (i)).hom ≫ (eL).hom)
      (eB ≫ diag) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (dgOdotMilnorRightAxisCompletedDiagonalComparison R d)
      ((congrArg (fun k => k ≫ (eL).hom) hi.symm).trans (Category.assoc _ _ _)) rfl
  have hright : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (eF.hom ≫ (dgOdotMilnorActualRightSourceEquivalence R d).hom ≫ diag)
      (eB ≫ diag) := cancelPrefix eF eB diag
  exact functorIsoReflectPreEquivalence eF (hleft.trans hright.symm)

/-- 概要：実包含辺の区間比較は元始域・中央成分の全経路を保持する。
方針：同じ実包含全比較を指定二成分付き証人へ渡す。
規約：元全ホモトピーを保持。使われ方：四辺境界の包含側 prism。 -/
def dgOdotMilnorActualRightInclusionWitness : PerfectStableArrowSquareWitness
    (dgKInputNuMap R (i)) (IdentityLax.exactDiagonal (Q))
    (dgOdotMilnorActualRightSourceMap R d) (dgOdotMilnorActualRightMiddleMap R d)
    (dgKInputStableValue_isIdempotentComplete R (A))
    (dgKInputStableValue_isIdempotentComplete R (B)) (hQ) (hΛ) :=
  perfectStableArrowSquareWitness _ _ _ _ _ _ _ _
    (dgOdotMilnorActualRightInclusionLaxComparison R d)

/-- 概要：実商辺の区間比較は同じ中央・終域成分の全経路を保持する。
方針：元実差全比較の逆を同じ指定二成分付き証人へ渡す。
規約：包含側と同じ中央成分。使われ方：四辺境界の商側 prism。 -/
def dgOdotMilnorActualRightProjectionWitness : PerfectStableArrowSquareWitness
    (dgKInputNuMap R (q)) (exactLaxDifference (𝟙 (Q)) (𝟙 (Q)))
    (dgOdotMilnorActualRightMiddleMap R d) (dgOdotMilnorActualRightTargetMap R d)
    (dgKInputStableValue_isIdempotentComplete R (B))
    (dgKInputStableValue_isIdempotentComplete R (D)) (hΛ) (hQ) :=
  perfectStableArrowSquareWitness _ _ _ _ _ _ _ _
    (dgOdotMilnorRightAxisCompletedDifferenceComparison R d).symm

end SerrePositivity.KST.SConstruction
