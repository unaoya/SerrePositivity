module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CoherentArrowStrings
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.OrdinaryComparisonPrism
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # 元の射から始まる合成列パラメータの収縮
概要：元の射そのものを合成列の精密化の初対象とし、全合成列へ向かう実収縮を構成する。
方針：二端点への標準射が唯一の精密化であることと、その自然変換の nerve を使う。
規約：合成列の辺や高次入力を選び直さず、長さ零の列も保持する。
使われ方：元の高次 K prism の全合成列を共通パラメータで評価する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {I : Type u} [SmallCategory I] {x y : I}

/-- 元の射そのものを長さ一の合成列とする。 -/
def coherentArrowStringDirect (f : x ⟶ y) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f where
  length := 1
  chain := (nerve.edgeMk f).edge
  long_edge := by simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap_one, op_id,
    CategoryTheory.Functor.map_id_apply]

/-- 元の射から任意の元の合成列へ向かう、二端点を選ぶ精密化。 -/
def coherentArrowStringDirectTo {f : x ⟶ y} (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) :
    coherentArrowStringDirect f ⟶ s where
  map := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap s.length
  first := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap_first _
  last := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap_last _
  comm := s.long_edge

/-- 元の射から合成列への端点固定の精密化は一意。 -/
lemma coherentArrowStringDirectTo_unique {f : x ⟶ y} (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)
    (a : coherentArrowStringDirect f ⟶ s) : a = coherentArrowStringDirectTo s := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.ext
  apply SimplexCategory.Hom.ext_one_left
  · exact a.first.trans (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap_first _).symm
  · exact a.last.trans (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap_last _).symm

/-- 元の射そのものは、全合成列と両端固定の精密化の圏の初対象。 -/
def coherentArrowStringDirect_isInitial (f : x ⟶ y) :
    IsInitial (coherentArrowStringDirect f) :=
  IsInitial.ofUniqueHom (fun s => coherentArrowStringDirectTo s)
    (fun s a => coherentArrowStringDirectTo_unique s a)

/-- 元の射から全合成列への精密化を一つの自然変換へ束ねる。 -/
def coherentArrowStringContractionTransformation (f : x ⟶ y) :
    (Functor.const (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)).obj (coherentArrowStringDirect f) ⟶
      𝟭 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) where
  app s := coherentArrowStringDirectTo s
  naturality _s _t _a := (coherentArrowStringDirect_isInitial f).hom_ext _ _

/-- 元の射への定値関手の nerve は、同じ元の頂点への定値単体射そのもの。 -/
lemma coherentArrowStringConstant_nerve (f : x ⟶ y) :
    nerveMap ((Functor.const (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)).obj (coherentArrowStringDirect f)) =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j a
  exact (coherentArrowStringDirect_isInitial f).hom_ext _ _

/-- 全合成列パラメータの元の射から始まる実際の単体的収縮。 -/
def coherentArrowStringContraction (f : x ⟶ y) :
    SSet.Homotopy (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f)))
      (𝟙 (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f))) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.ordinaryComparisonHomotopy (coherentArrowStringContractionTransformation f)
  exact
    { h := H.h
      h₀ := H.h₀.trans (coherentArrowStringConstant_nerve f)
      h₁ := H.h₁
      rel := H.rel }

end SerrePositivity.KST.SConstruction
