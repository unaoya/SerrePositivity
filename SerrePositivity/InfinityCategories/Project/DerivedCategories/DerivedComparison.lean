module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeSubcategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeKProjective
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeResolution
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Semifree 複体の H⁰ と導来圏の同値 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 概要：semifree 複体の H⁰ を Mathlib の導来圏へ送る比較関手。
方針：ホモトピー圏への包含に局所化関手 `Qh` を合成する。
規約：導来圏の宇宙は `HasDerivedCategory` で指定する。
使われ方：semifree 導来同値の順関手。 -/
def semifreeDerivedComparison :
    DifferentialGraded.HomotopyCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) ⥤ DerivedCategory (ModuleCat S) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S ⋙ DerivedCategory.Qh

/-- 概要：semifree 導来比較は各 Hom 上で全単射である。
方針：semifree の K-projective 性から `Qh` の Hom 全単射を使う。
規約：対象は任意の semifree 複体。使われ方：比較の充満忠実性。 -/
theorem semifreeDerivedComparison_map_bijective
    (X Y : DifferentialGraded.HomotopyCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)) :
    Function.Bijective ((semifreeDerivedComparison S).map :
      (X ⟶ Y) → ((semifreeDerivedComparison S).obj X ⟶
        (semifreeDerivedComparison S).obj Y)) := by
  obtain ⟨X⟩ := X
  let P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S := ForgetEnrichment.to (Complex S) X
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_isKProjective S P.property
  exact (CochainComplex.IsKProjective.Qh_map_bijective P.val
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).obj Y)).comp
      ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).map_injective,
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).map_surjective⟩

/-- 概要：semifree 導来比較は充満である。
方針：Hom 全単射の全射部分を使う。規約：導来圏は指定済み。
使われ方：比較の圏同値への昇格。 -/
instance semifreeDerivedComparisonFull : (semifreeDerivedComparison S).Full where
  map_surjective {X Y} := (semifreeDerivedComparison_map_bijective S X Y).surjective

/-- 概要：semifree 導来比較は忠実である。
方針：Hom 全単射の単射部分を使う。規約：導来圏は指定済み。
使われ方：比較の圏同値への昇格。 -/
instance semifreeDerivedComparisonFaithful : (semifreeDerivedComparison S).Faithful where
  map_injective {X Y} := (semifreeDerivedComparison_map_bijective S X Y).injective

/-- 概要：導来圏の任意の対象は semifree 複体で代表される。
方針：`Q` の代表に semifree 解像度を取り、擬同型の像の同型を合成する。
規約：解像度に有界性を課さない。使われ方：比較の本質的全射性。 -/
instance semifreeDerivedComparisonEssSurj : (semifreeDerivedComparison S).EssSurj where
  mem_essImage X := by
    obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
      (DerivedCategory.Q (C := ModuleCat S)) X
    obtain ⟨P, q, hP, _, hq⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.exists_complexSemifree_resolution S M
    let := hq
    refine ⟨(toHomotopy S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)).obj
      (ForgetEnrichment.of (Complex S) (⟨P, hP⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)), ⟨?_⟩⟩
    exact (DerivedCategory.quotientCompQhIso (ModuleCat S)).app P ≪≫
      asIso (DerivedCategory.Q.map q) ≪≫ e

/-- 概要：semifree 導来比較は圏同値を定める。
方針：充満・忠実・本質的全射を組み合わせる。規約：追加の数学的仮定なし。
使われ方：標準の逆関手と単位・余単位の構成。 -/
instance semifreeDerivedComparisonIsEquivalence :
    (semifreeDerivedComparison S).IsEquivalence where

/-- 概要：semifree 複体の H⁰ は通常の非有界導来圏と圏同値である。
方針：K-projective 性による充満忠実性と semifree 解像度による本質的全射性。
規約：可換環上で、導来圏の選択だけを instance として受け取る。
使われ方：後の導来 ∞ 圏のホモトピー圏の同定。 -/
def semifreeDerivedEquivalence :
    DifferentialGraded.HomotopyCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) ≌ DerivedCategory (ModuleCat S) :=
  (semifreeDerivedComparison S).asEquivalence

end SerrePositivity.InfinityCategories.Project.DerivedCategories
