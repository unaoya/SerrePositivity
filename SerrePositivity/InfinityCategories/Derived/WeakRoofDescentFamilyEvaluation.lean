module
public import SerrePositivity.InfinityCategories.Derived.KanPrecompositionHomotopyIso
public import SerrePositivity.InfinityCategories.Derived.WeakRoofDescentRestriction

/-! # 任意パラメータ族の全降下選択空間上の評価比較

概要：商側・標的側の指定実ホモトピーから、全パラメータと降下選択空間上の同じ評価比較を得る。
方針：Kan な関手空間内の実辺と二段降下の普遍比較を接続する。
規約：パラメータごとに選び直さない。使われ方：任意標的での実屋根評価と合成の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
/-- 内部 Hom の二段の前合成は、同じ指定二射の合成による前合成。 -/
lemma roofPrecomposition_comp {A B C Z : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (pre g).app Z ≫ (pre f).app Z = (pre (f ≫ g)).app Z := by
  rw [← NatTrans.comp_app, ← pre_map]
/-- 二つの全パラメータ実比較は、全降下選択空間上で作用族と指定評価族を比較する。 -/
def weakRoofDescentActionFamilyEvaluationIso {R Q E Z H K : SSet.{u}} [KanComplex Z]
    (w : R ⟶ Q) (i : Z ⟶ E) (t : R ⟶ E) (j : H ⟶ Q)
    (a : K ⟶ R) (b : K ⟶ H) (c : K ⟶ Z)
    (HQ : SSet.Homotopy (a ≫ w) (b ≫ j)) (HE : SSet.Homotopy (a ≫ t) (c ≫ i)) :
    FunctorIso (weakRoofDescentAction w i t j ≫ (pre b).app Z)
      (SSet.const (functorVertex c)) := by
  have hQ := FunctorIso.precomp (kanPrecompositionHomotopyIso (Z := Z) HQ)
    (weakRoofDescentExtension w i t)
  have hD := FunctorIso.postcomp (weakRoofDescentExtensionIso w i t) ((pre a).app Z)
  have hE := FunctorIso.precomp (kanPrecompositionHomotopyIso (Z := Z) HE)
    (weakRoofDescentEvaluation w i t)
  have hI := FunctorIso.postcomp (weakRoofDescentEvaluationIso w i t) ((pre c).app Z)
  have hc : SSet.const (X := weakRoofDescentSpace w i t) (functorVertex (𝟙 Z)) ≫
      (pre c).app Z = SSet.const (functorVertex c) := by
    rw [SSet.const_comp]
    change SSet.const (functorVertex (c ≫ 𝟙 Z)) = _
    rw [Category.comp_id]
  rw [hc] at hI
  simp only [Category.assoc, roofPrecomposition_comp] at hD hI
  simpa only [weakRoofDescentAction, Category.assoc, roofPrecomposition_comp] using
    hQ.symm ≪≫ hD ≪≫ hE ≪≫ hI
end SerrePositivity.InfinityCategories
