module
public import SerrePositivity.KST.ProExcision.PropA1Naturality
public import SerrePositivity.KST.ProExcision.LinearizedBarMHomotopy
public import SerrePositivity.KST.ProExcision.HomologyModel
public import SerrePositivity.KST.ProExcision.RelativeBar

/-!
# Lemma A.4 の m 次同変ホモトピーによる零化

概要：homologically m-constant な同変射は次数 i≤m の半直積の相対ホモロジーで零を誘導する。
方針：係数の m 次ホモトピーを線形な bar へ持ち上げ、A.1 の自然性で半直積へ移し、分裂余核へ降ろす。
規約：KST Definition A.3、Lemma A.4。H_* の関手と自然な複体模型同定は K-L2 から借りる明示的な引数。
使われ方：KST Lemma 4.16 と Proposition 4.14 の同変な定数射への比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
open SerrePositivity.KST.Comparison
variable {G H H' : SimplicialObject MonCat.{u}}
variable {A : SimplicialMonoidAction G H} {B : SimplicialMonoidAction G H'}

/-- 概要：同変射が homologically m-constant であるという数学的データ。
方針：C(φ) と C(e) の m 次ホモトピーと、その区間写像の G 同変性を保持する。
規約：KST Definition A.3、零次を含む非被約 C(H)。H_* の結論や bar への持ち上げは含めない。
使われ方：Lemma A.4 の入力と Lemma 4.16 の出力。 -/
structure HomologicallyMConstant (f : SimplicialActionHom A B) (m : ℕ) where
  homotopy : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (monoidBarMap f.hom))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (monoidBarMap (SimplicialActionHom.trivial A B).hom)) m
  equivariant (n : SimplexCategoryᵒᵖ) (a : G.obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (linearizedSetAction (barSetAction A) n a) (𝟙 _) ≫ homotopy.h.app n =
      homotopy.h.app n ≫ linearizedSetAction (barSetAction B) n a

/-- 概要：m 次同変ホモトピーは半直積の絶対ホモロジー項で自明射との一致を与える。
方針：線形に持ち上げた bar のホモトピーを、模型同型と A.1 の自然性で移す。
規約：KST Lemma A.4 の絶対項。F の反転性と模型同定は H_* 所有レーンの界面。
使われ方：相対余核での零化の前段。 -/
theorem lemmaA4_absolute (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    (hF : SSet.anodyneExtensions.IsInvertedBy F) {i : ℕ} (M : SimplicialHomologyModel F i)
    (hG : SimplicialMonoid.IsGrouplike G) (f : SimplicialActionHom A B) {m : ℕ}
    (hf : HomologicallyMConstant f m) (hi : i ≤ m) :
    F.map (monoidBarMap (simplicialActionProductMap f)) =
      F.map (monoidBarMap (simplicialActionProductMap (SimplicialActionHom.trivial A B))) := by
  let e := SimplicialActionHom.trivial A B
  have hbar : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (coefficientActionBarMap f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (coefficientActionBarMap e)) m :=
    linearizedActionBarMHomotopy (barSetActionHom f) (barSetActionHom e) rfl rfl
      hf.homotopy hf.equivariant
  have hc := M.map_eq_of_mHomotopy hbar hi
  apply (cancel_epi (propA1ComparisonIso F hF A hG).hom).mp
  rw [← propA1ComparisonIso_naturality F hF hG f,
    ← propA1ComparisonIso_naturality F hF hG e, hc]

/-- 概要：homologically m-constant な射は次数 i≤m の相対半直積ホモロジーで零を誘導する。
方針：絶対項の自明射との一致を分裂包含の余核へ降ろす。
規約：KST Lemma A.4。相対項は所有レーンの F の像の分裂余核模型。
使われ方：KST Proposition 4.14、Lemma 4.16 の同変射のホモロジー零化。 -/
theorem lemmaA4 (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    (hF : SSet.anodyneExtensions.IsInvertedBy F) {i : ℕ} (M : SimplicialHomologyModel F i)
    (hG : SimplicialMonoid.IsGrouplike G) (f : SimplicialActionHom A B) {m : ℕ}
    (hf : HomologicallyMConstant f m) (hi : i ≤ m) : relativeBarMap F f = 0 :=
  relativeBarMap_zero_of_absolute_eq_trivial F f (lemmaA4_absolute F hF M hG f hf hi)

end SerrePositivity.KST.ProExcision
