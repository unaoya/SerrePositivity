module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorOverUniverseNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws

/-!
概要：相対後合成は元の宇宙変更および底上の同型による表示変更に自然である。
方針：宇宙変更は包含後の単体で計算し、表示変更は前後合成則に帰着する。
規約：全空間の元の同型と可換四角形を保持する。
使われ方：G14 の元の小さい Yoneda 評価への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 同じ底上の同型と可換四角形による相対 Hom の表示変更は、後合成に自然。 -/
lemma relativeFunctorOverIso_post_hom {B : SSet.{u}}
    {a a' b b' c c' : Over B} (ea : a ≅ a') (eb : b ≅ b') (ec : c ≅ c')
    (f : b ⟶ c) (g : b' ⟶ c') (h : eb.hom ≫ g = f ≫ ec.hom) :
    relativeFunctorPost b.hom c.hom f.left f.w a.hom ≫ (relativeFunctorOverIso ea ec).hom =
      (relativeFunctorOverIso ea eb).hom ≫
        relativeFunctorPost b'.hom c'.hom g.left g.w a'.hom := by
  rw [relativeFunctorOverIso_hom, relativeFunctorOverIso_hom,
    ← Category.assoc, ← relativeFunctorPost_overPre, Category.assoc]
  simp only [Category.assoc]
  rw [relativeFunctorPost_comp, relativeFunctorPost_comp]
  have hh := congrArg
    (fun t : b ⟶ c' => relativeFunctorPost b.hom c'.hom t.left t.w a'.hom) h
  exact congrArg (fun k => relativeFunctorOverPre b.hom ea.inv ≫ k) hh.symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
