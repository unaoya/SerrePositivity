module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordComposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentAdjacent
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentUnits
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# 元の左の弱同値を持つ二列の roof

概要：元の X←U→Y と全縦弱同値を同じ二列の zigzag にする。
方針：三頂点と元の二射をそのまま使う。
規約：元の終域と元の中間射を保持する。
使われ方：恒等右脚の source frame 比較の全端点自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v uI vI
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof
open CategoryTheory

def word : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := ⟨2, ![.backward, .forward]⟩

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {X Y U V : C}

variable [W.IsMultiplicative]

def obj (p : U ⟶ X) (hp : W p) (f : U ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W word X Y where
  vertex := ![X, U, Y]
  first := rfl
  last := rfl
  arrow := Fin.cases p (Fin.cases f (fun i => Fin.elim0 i))
  backward_mem i hi := by
    fin_cases i
    · exact hp
    · cases hi

def map {p : U ⟶ X} {q : V ⟶ X} {hp : W p} {hq : W q}
    {f : U ⟶ Y} {g : V ⟶ Y} (a : U ⟶ V) (ha : W a)
    (hpa : a ≫ q = p) (hfa : f = a ≫ g) : obj W p hp f ⟶ obj W q hq g where
  app := Fin.cases (𝟙 X) (Fin.cases a (Fin.cases (𝟙 Y) (fun i => Fin.elim0 i)))
  app_mem i := by
    fin_cases i
    · exact W.id_mem X
    · exact ha
    · exact W.id_mem Y
  first := rfl
  last := rfl
  comm i := by
    fin_cases i
    · exact (Category.comp_id _).trans hpa.symm
    · exact (Category.comp_id _).trans hfa

def diagram {I : Type uI} [Category.{vI} I] (U : I ⥤ C)
    (p : U ⟶ (Functor.const I).obj X) (hp : ∀ i, W (p.app i))
    (f : U ⟶ (Functor.const I).obj Y) (hU : ∀ {i j} (a : i ⟶ j), W (U.map a)) :
    I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W word X Y where
  obj i := obj W (p.app i) (hp i) (f.app i)
  map {i j} a := map W (hp := hp i) (hq := hp j) (f := f.app i) (g := f.app j)
    (U.map a) (hU a)
    (by
      have h := p.naturality a
      change U.map a ≫ p.app j = p.app i ≫ 𝟙 X at h
      exact h.trans (Category.comp_id _))
    (by
      have h := f.naturality a
      change U.map a ≫ f.app j = f.app i ≫ 𝟙 Y at h
      exact (h.trans (Category.comp_id _)).symm)
  map_id i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (by
    intro j
    fin_cases j
    · rfl
    · exact U.map_id i
    · rfl)
  map_comp a b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (by
    intro j
    fin_cases j
    · exact (Category.id_comp _).symm
    · exact U.map_comp a b
    · exact (Category.id_comp _).symm)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof
