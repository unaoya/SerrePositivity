module

public import SerrePositivity.EInfinity.SimplicialLocalization.UnmarkedGeneratorFunctor
public import SerrePositivity.EInfinity.Hammock.UnmarkedGeneratorColumns
public import SerrePositivity.EInfinity.Hammock.HammockValue

/-!
# 元の全語の hammock の非指定生成文字列への評価

概要：全縦射・全語の合成と恒等列の挿入に不変な非指定文字列を元の余極限から得る。
方針：指定射列を恒等射へ送る元の関手を、既存の zigzag の評価へ代入する。
規約：全語・元の標準射・reduced 正規化・augmentation への回収式を保持する。
使われ方：hammock の元の自由積分解の添字。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C}

def value (S : Zigzag W.paths w X Y) : List (Quiver.Total C) :=
  Zigzag.Value.value (GeneratorWord.functor W) (GeneratorWord.inverts W) S

lemma value_hom {S T : Zigzag W.paths w X Y} (f : S ⟶ T) : value W S = value W T :=
  Zigzag.Value.value_eq (GeneratorWord.functor W) (GeneratorWord.inverts W) f

lemma value_wordAction {a b : Word} (f : a ⟶ b) (S : Zigzag W.paths a X Y) :
    value W (WordAction.obj f S) = value W S :=
  Zigzag.Value.wordAction_value (GeneratorWord.functor W) (GeneratorWord.inverts W) f S

def graphValue : graph W.paths w X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (List (Quiver.Total C)) :=
  Zigzag.Value.graphMap (GeneratorWord.functor W) (GeneratorWord.inverts W)

def colimitValue (X Y : Paths C) : colimitGraph W.paths X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (List (Quiver.Total C)) :=
  Zigzag.Value.colimitValue (GeneratorWord.functor W) (GeneratorWord.inverts W) X Y

lemma graphInclusion_colimitValue (X Y : Paths C) (w : Word) :
    graphInclusion W.paths X Y w ≫ colimitValue W X Y = graphValue W :=
  Zigzag.Value.graphInclusion_colimitValue (GeneratorWord.functor W) (GeneratorWord.inverts W) X Y w

def reducedValue (X Y : Paths C) : reducedSimplicialSet W.paths X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (List (Quiver.Total C)) :=
  Zigzag.Value.reducedValue (GeneratorWord.functor W) (GeneratorWord.inverts W) X Y

lemma graphNormalization_reducedValue (X Y : Paths C) (w : Word) :
    graphNormalization W.paths X Y w ≫ reducedValue W X Y = graphValue W :=
  Zigzag.Value.graphNormalization_reducedValue (GeneratorWord.functor W)
    (GeneratorWord.inverts W) X Y w

lemma colimitNormalization_reducedValue (X Y : Paths C) :
    colimitNormalization W.paths X Y ≫ reducedValue W X Y = colimitValue W X Y :=
  Zigzag.Value.colimitNormalization_reducedValue (GeneratorWord.functor W)
    (GeneratorWord.inverts W) X Y

lemma edge_forward (S : Zigzag W.paths w X Y) (i : Fin w.length)
    (hi : w.direction i = .forward) :
    Zigzag.Value.edge (GeneratorWord.functor W) (GeneratorWord.inverts W) S i =
      GeneratorWord.erase W (Direction.arrow .forward S i hi) :=
  Zigzag.Value.edge_forward (GeneratorWord.functor W) (GeneratorWord.inverts W) S i hi

lemma edge_backward (S : Zigzag W.paths w X Y) (i : Fin w.length)
    (hi : w.direction i = .backward) :
    Zigzag.Value.edge (GeneratorWord.functor W) (GeneratorWord.inverts W) S i = [] := by
  rw [Zigzag.Value.edge_backward (GeneratorWord.functor W) (GeneratorWord.inverts W) S i hi]
  have hm : (Zigzag.Value.backwardIso (GeneratorWord.functor W)
      (GeneratorWord.inverts W) S i hi).hom = [] :=
    GeneratorWord.erase_marked W (Direction.arrow .backward S i hi).unop
      (Direction.arrow_allowed .backward S i hi)
  have he := (Zigzag.Value.backwardIso (GeneratorWord.functor W)
    (GeneratorWord.inverts W) S i hi).hom_inv_id
  change _ ++ _ = ([] : List (Quiver.Total C)) at he
  rw [hm, List.nil_append] at he
  exact he

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
