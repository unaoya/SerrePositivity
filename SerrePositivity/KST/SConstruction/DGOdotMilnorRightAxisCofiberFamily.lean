module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeCofiberFamily
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisFullConeSquare

/-!
概要：元 Milnor 右軸の同じ実 cone 全族を Sp 正本の cofiber 空間と選択図式へ接続する。
方針：元実商延長の全厳密変換を、同じ底辺を保つ全図式比較へ代入する。
規約：元両二胞体・元零角を保持。Cat^perf 長方形認証とは区別する。
使われ方：元実逆回転と固定 ν の全図式接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories
open LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "P" => DGCategoryCellResolution.Source R (DGOdotGluing R d)
local notation "Q" => DGQuotient.QuotientObject (P)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local notation "I" => perfectDGModuleInclusion R (Q) Set.univ
local notation "F" => DGFunctor.comp (dgOdotMilnorRightAxisQuotientSource R d) (I)
local notation "G" => DGFunctor.comp (dgOdotMilnorRightAxisQuotientTarget R d) (I)
local notation "η" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp
  (dgOdotMilnorRightAxisQuotientStrictNatTrans R d) (I)
local notation "X" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R (Q))

/-- 概要：元実商上の同じ cone 全族の Sp 正本 cofiber 空間への持ち上げ。
方針：同じ全図式・同じ全自然性を特殊化する。
規約：追加主仮定なし。使われ方：元全逆回転の普遍比較。 -/
def dgOdotMilnorRightAxisCofiberFamily : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (P) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.space (X) :=
  dgModuleNaturalConeCofiberFamily R (Q) (P) (F) (G) (η)

/-- 概要：同じ元 cofiber 全族を含めると元全四角形の交換族を回収する。
方針：同じ full subcomplex の厳密回収則を使用する。
規約：元両二胞体を保持。使われ方：元指定面の全接続。 -/
lemma dgOdotMilnorRightAxisCofiberFamily_inclusion :
    dgOdotMilnorRightAxisCofiberFamily R d ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.inclusion (X) =
      dgModuleNaturalConeSquareFamily R (Q) (P) (F) (G) (η) :=
  dgModuleNaturalConeCofiberFamily_inclusion R (Q) (P) (F) (G) (η)

/-- 概要：元同じ cone 全図式と同じ底辺を保つ選択 cofiber 全図式との全比較。
方針：Sp 正本の相対図式比較を元実商延長へ特殊化する。
規約：元両二胞体を保持。Cat^perf の第三認証は別工程。
使われ方：元実逆回転と固定 ν の中央比較。 -/
def dgOdotMilnorRightAxisCofiberFamilyComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgOdotMilnorRightAxisCofiberFamily R d ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.inclusion (X))
    (CofiberDiagrams.lift (X)
      (dgOdotMilnorRightAxisCofiberFamily R d ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom (X)) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.inclusion (X)) :=
  dgModuleNaturalConeCofiberFamilyComparison R (Q) (P) (F) (G) (η)

end SerrePositivity.KST.SConstruction
