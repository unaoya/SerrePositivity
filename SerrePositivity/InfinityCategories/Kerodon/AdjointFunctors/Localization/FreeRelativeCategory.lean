module

public import Mathlib.CategoryTheory.Category.Quiv
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Dwyer–Kan の自由相対圏とその余単位・対角

概要：Dwyer–Kan の自由単体的解像の基礎となる自由相対圏を構成する。
方針：自由圏の射は元の矢の列、指定する弱同値は全矢が元の弱同値である列とする。
規約：自由圏の Hom 宇宙は対象・元の Hom の宇宙の最大値。
使われ方：反復自由圏の各次数と単体作用素の構成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section

universe u v u' v'

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} {V : MorphismProperty D}

/-- 概要：相対関手は自由相対圏の間の関手へ持ち上がる（Dwyer–Kan）。
方針：元の各矢の像を列の全矢へ適用する。
規約：自由圏の弱同値は W.paths で、全矢の条件を保持する。
使われ方：反復自由相対圏の関手性。 -/
def freeRelativeMap (F : LocalizerMorphism W V) : LocalizerMorphism W.paths V.paths where
  functor := Cat.freeMap F.functor.toPrefunctor
  map _ _ p hp := by
    induction p with
    | nil => trivial
    | cons p f ih => exact ⟨ih hp.1, F.map f hp.2⟩

/-- 概要：自由相対圏の余単位は元の列の合成（Dwyer–Kan）。
方針：弱同値の恒等射・合成閉性を列の長さに沿って使う。
規約：元の弱同値類の乗法性だけを要求する。
使われ方：自由解像の面写像と元の相対圏への augmentation。 -/
def freeCounit (W : MorphismProperty C) [W.IsMultiplicative] :
    LocalizerMorphism W.paths W where
  functor := pathComposition C
  map _ _ p hp := by
    induction p with
    | nil => exact W.id_mem _
    | cons p f ih => exact W.comp_mem _ _ (ih hp.1) hp.2

/-- 概要：自由相対圏の対角は各矢を一文字の列にする（Dwyer–Kan）。
方針：各生成矢をその一文字の列へ送り、列全体に自由関手を適用する。
規約：元の弱同値類の乗法性は不要。
使われ方：自由解像の退化写像。 -/
def freeDiagonal (W : MorphismProperty C) : LocalizerMorphism W.paths W.paths.paths where
  functor := Cat.freeMap (Paths.of C)
  map _ _ p hp := by
    induction p with
    | nil => trivial
    | cons p f ih => exact ⟨ih hp.1, ⟨trivial, hp.2⟩⟩

/-- 概要：自由化は相対関手の恒等関手を保つ（Dwyer–Kan）。
方針：同じ自由関手の恒等則を使う。
規約：相対圏の弱同値類も同じ W.paths。
使われ方：反復自由解像の関手性。 -/
lemma freeRelativeMap_id (W : MorphismProperty C) :
    (freeRelativeMap (LocalizerMorphism.id W)).functor = 𝟭 (Paths C) :=
  Cat.freeMap_id C

/-- 概要：自由化は相対関手の合成を保つ（Dwyer–Kan）。
方針：元の自由関手の合成則を使う。
規約：元の射の列をそのまま送る。
使われ方：単体作用素と係数関手の合成則。 -/
lemma freeRelativeMap_comp {E : Type*} [Category E] {U : MorphismProperty E}
    (F : LocalizerMorphism W V) (G : LocalizerMorphism V U) :
    (freeRelativeMap (F.comp G)).functor =
      (freeRelativeMap F).functor ⋙ (freeRelativeMap G).functor :=
  Cat.freeMap_comp F.functor.toPrefunctor G.functor.toPrefunctor

/-- 概要：余単位は元の相対関手に厳密に自然（Dwyer–Kan）。
方針：列の合成と元の関手の合成保存を使う。
規約：自然同型だけでなく同じ関手の等式。
使われ方：自由解像の面と係数射の整合性。 -/
lemma freeCounit_naturality [W.IsMultiplicative] [V.IsMultiplicative]
    (F : LocalizerMorphism W V) :
    (freeRelativeMap F).functor ⋙ (freeCounit V).functor =
      (freeCounit W).functor ⋙ F.functor :=
  Quiv.pathComposition_naturality F.functor

/-- 概要：自由相対圏の対角は元の相対関手に厳密に自然（Dwyer–Kan）。
方針：生成矢の一文字の列への写像の自然性を自由化する。
規約：元の弱同値類の乗法性は不要。
使われ方：自由解像の退化と係数関手の整合性。 -/
lemma freeDiagonal_naturality (F : LocalizerMorphism W V) :
    (freeRelativeMap F).functor ⋙ (freeDiagonal V).functor =
      (freeDiagonal W).functor ⋙ (freeRelativeMap (freeRelativeMap F)).functor := by
  change Cat.freeMap F.functor.toPrefunctor ⋙ Cat.freeMap (Paths.of D) =
    Cat.freeMap (Paths.of C) ⋙ Cat.freeMap (Cat.freeMap F.functor.toPrefunctor).toPrefunctor
  rw [← Cat.freeMap_comp, ← Cat.freeMap_comp]
  exact congrArg Cat.freeMap
    (Quiv.pathsOf_freeMap_toPrefunctor F.functor.toPrefunctor).symm

/-- 概要：対角と自由圏での余単位の合成は恒等（Dwyer–Kan）。
方針：自由・忘却随伴の元の三角恒等式を使う。
規約：同じ生成矢と列の結合を使う。
使われ方：単体的解像の一方の面退化恒等式。 -/
lemma freeDiagonal_left_counit (W : MorphismProperty C) :
    (freeDiagonal W).functor ⋙ (freeCounit W.paths).functor = 𝟭 (Paths C) :=
  Quiv.freeMap_pathsOf_pathComposition C

/-- 概要：対角と自由化した余単位の合成は恒等（Dwyer–Kan）。
方針：自由化の合成則と元の三角恒等式を合成する。
規約：同じ相対関手の厳密な等式。
使われ方：単体的解像のもう一方の面退化恒等式。 -/
lemma freeDiagonal_right_counit (W : MorphismProperty C) [W.IsMultiplicative] :
    (freeDiagonal W).functor ⋙ (freeRelativeMap (freeCounit W)).functor = 𝟭 (Paths C) := by
  change Cat.freeMap (Paths.of C) ⋙ Cat.freeMap (pathComposition C).toPrefunctor = _
  rw [← Cat.freeMap_comp, Quiv.pathsOf_pathComposition_toPrefunctor, Cat.freeMap_id]

/-- 概要：自由相対圏の対角は余結合的（Dwyer–Kan）。
方針：生成矢を一文字の列へ送る比較の自然性を自由化する。
規約：等式は実際の関手の厳密な等式。
使われ方：単体的解像の退化写像同士の恒等式。 -/
lemma freeDiagonal_coassoc (W : MorphismProperty C) :
    (freeDiagonal W).functor ⋙ (freeRelativeMap (freeDiagonal W)).functor =
      (freeDiagonal W).functor ⋙ (freeDiagonal W.paths).functor := by
  change Cat.freeMap (Paths.of C) ⋙ Cat.freeMap (Cat.freeMap (Paths.of C)).toPrefunctor =
    Cat.freeMap (Paths.of C) ⋙ Cat.freeMap (Paths.of (Paths C))
  rw [← Cat.freeMap_comp, ← Cat.freeMap_comp]
  exact congrArg Cat.freeMap (Quiv.pathsOf_freeMap_toPrefunctor (Paths.of C))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
