module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.HTT.Section6_1_2.OppositeIso
public import Mathlib.CategoryTheory.Category.Cat.Op

/-!
概要：反転した Bousfield–Kan 重みを、同じ Under 圏の nerve で表示する。
方針：Mathlib の指定 Over・Under 反転同値と既存の nerveUnopIso を合成する。
規約：Kerodon §7.5.1（Tag 03A0）の元の重みの係数移送の法則。
使われ方：集合値係数の coend と既存の simplicial replacement の同じ模型の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.HTT.Section6_1_2
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable (I : Type u) [SmallCategory I]

/-- 既存の指定反転同値の単位・余単位は恒等なので、同じ通常圏の同型になる。 -/
def overUnderOppositeCatIso (i : I) :
    Cat.of (Over (Opposite.op i)) ≅ Cat.of ((Under i)ᵒᵖ) where
  hom := (Over.opEquivOpUnder i).functor.toCatHom
  inv := (Over.opEquivOpUnder i).inverse.toCatHom
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- 同じ重みの成分を Under の nerve へ戻す。 -/
def reflectedBousfieldKanUnderIso (i : I) :
    ((bousfieldKanWeight Iᵒᵖ).obj (Opposite.op i)).op ≅ nerve (Under i) :=
  SSet.opFunctor.mapIso (nerveFunctor.mapIso (overUnderOppositeCatIso I i)) ≪≫
    nerveUnopIso (Under i)

/-- 元の Over の後合成と Under の前合成は、指定反転の同じ四角形。 -/
lemma overUnderOppositeCatIso_naturality {i j : I} (f : i ⟶ j) :
    nerveMap (Over.map f.op) ≫ (nerveFunctor.mapIso (overUnderOppositeCatIso I i)).hom =
      (nerveFunctor.mapIso (overUnderOppositeCatIso I j)).hom ≫
        nerveMap (Under.map f).op := by
  change nerveMap (Over.map f.op) ≫ nerveMap (Over.opEquivOpUnder i).functor =
    nerveMap (Over.opEquivOpUnder j).functor ≫ nerveMap (Under.map f).op
  calc
    _ = nerveMap (Over.map f.op ⋙ (Over.opEquivOpUnder i).functor) :=
      (nerveFunctor.map_comp (Over.map f.op).toCatHom
        (Over.opEquivOpUnder i).functor.toCatHom).symm
    _ = nerveMap ((Over.opEquivOpUnder j).functor ⋙ (Under.map f).op) := rfl
    _ = _ := nerveFunctor.map_comp (Over.opEquivOpUnder j).functor.toCatHom
      (Under.map f).op.toCatHom

/-- 反転 BK 重みと Under 重みの比較は、全ての添字の射に自然。 -/
def reflectedBousfieldKanUnderWeightIso :
    bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor ≅ Under.mapFunctor I ⋙ nerveFunctor :=
  NatIso.ofComponents (fun i => reflectedBousfieldKanUnderIso I i.unop) (by
    intro i j f
    change SSet.opFunctor.map (nerveMap (Over.map f)) ≫
      (SSet.opFunctor.map (nerveFunctor.mapIso (overUnderOppositeCatIso I j.unop)).hom ≫
        (nerveUnopIso (Under j.unop)).hom) = _
    calc
      _ = SSet.opFunctor.map (nerveMap (Over.map f) ≫
          (nerveFunctor.mapIso (overUnderOppositeCatIso I j.unop)).hom) ≫
          (nerveUnopIso (Under j.unop)).hom := by
        rw [SSet.opFunctor.map_comp, Category.assoc]
      _ = SSet.opFunctor.map ((nerveFunctor.mapIso (overUnderOppositeCatIso I i.unop)).hom ≫
          nerveMap (Under.map f.unop).op) ≫ (nerveUnopIso (Under j.unop)).hom := by
        apply congrArg (fun g => SSet.opFunctor.map g ≫ (nerveUnopIso (Under j.unop)).hom)
        simpa only [Quiver.Hom.op_unop] using overUnderOppositeCatIso_naturality I f.unop
      _ = _ := by
        rw [SSet.opFunctor.map_comp, Category.assoc, nerveUnopIso_natural]
        rfl)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
