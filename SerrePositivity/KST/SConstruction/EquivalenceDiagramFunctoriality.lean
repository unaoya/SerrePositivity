module
public import SerrePositivity.KST.SConstruction.EquivalenceDiagrams

/-! # 全同値図式の添字への関手性
概要：D(m,w) を単体的図式としてまとめ、定数図式の包含の自然性を示す。
方針：全部分複体の包含後で内部 Hom の前合成の法則を使う。
規約：全ての面と退化を同時に扱う。使われ方：object/core の対角比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：全同値図式の恒等な添字制限は恒等射。
方針：包含後の前合成の恒等法則。
規約：全単体での等号。使われ方：D(m,w) の関手法則。 -/
lemma equivalenceDiagramReindex_id (K C : SSet.{u}) :
    equivalenceDiagramReindex (𝟙 K) C = 𝟙 (equivalenceDiagrams K C) := by
  have : Mono (equivalenceDiagramι K C) := by unfold equivalenceDiagramι; infer_instance
  apply (cancel_mono (equivalenceDiagramι K C)).1
  rw [equivalenceDiagramReindex_ι, pre_id]
  simp

/-- 概要：全同値図式の二段の添字制限は合成の制限。
方針：包含後で前合成の合成則を使う。
規約：任意の単体集合の射。使われ方：D(m,w) の面・退化の両立。 -/
lemma equivalenceDiagramReindex_comp {K L M : SSet.{u}} (i : L ⟶ K) (j : M ⟶ L)
    (C : SSet.{u}) :
    equivalenceDiagramReindex (j ≫ i) C = equivalenceDiagramReindex i C ≫
      equivalenceDiagramReindex j C := by
  have : Mono (equivalenceDiagramι M C) := by unfold equivalenceDiagramι; infer_instance
  apply (cancel_mono (equivalenceDiagramι M C)).1
  rw [equivalenceDiagramReindex_ι, Category.assoc, equivalenceDiagramReindex_ι,
    ← Category.assoc, equivalenceDiagramReindex_ι, pre_map, NatTrans.comp_app, Category.assoc]

/-- 概要：添字制限後の評価は元の添字の像の頂点での評価。
方針：前合成後の内部 Hom の評価の式。
規約：頂点は任意。使われ方：評価写像の相対比較。 -/
lemma equivalenceDiagramReindex_evaluation {K L : SSet.{u}} (i : L ⟶ K)
    (C : SSet.{u}) (l : L _⦋0⦌) :
    equivalenceDiagramReindex i C ≫ equivalenceDiagramEvaluation L C l =
      equivalenceDiagramEvaluation K C (i.app (Opposite.op ⦋0⦌) l) := by
  rw [equivalenceDiagramEvaluation, ← Category.assoc, equivalenceDiagramReindex_ι,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

/-- 概要：全同値な定数図式の包含は任意の添字制限と厳密に両立する。
方針：包含後で curry の前合成の式と第二射影を計算する。
規約：添字の頂点を固定する必要はない。使われ方：対角比較の自然な定数図式の包含。 -/
lemma equivalenceDiagramConstant_reindex {K L : SSet.{u}} (i : L ⟶ K) (C : SSet.{u}) :
    equivalenceDiagramConstant K C ≫ equivalenceDiagramReindex i C =
      equivalenceDiagramConstant L C := by
  have : Mono (equivalenceDiagramι L C) := by unfold equivalenceDiagramι; infer_instance
  apply (cancel_mono (equivalenceDiagramι L C)).1
  rw [Category.assoc, equivalenceDiagramReindex_ι, ← Category.assoc,
    equivalenceDiagramConstant_ι, equivalenceDiagramConstant_ι]
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
  rfl

/-- 概要：全同値な標準単体の図式 D(m,w) を m に関する単体的図式にまとめる。
方針：全ての標準単体の射による前合成。
規約：図式間の自然変換は可逆に制限しない。使われ方：object/core 比較の二重単体集合。 -/
def simplicialEquivalenceDiagrams (C : SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj n := equivalenceDiagrams (stdSimplex.obj n.unop) C
  map α := equivalenceDiagramReindex (stdSimplex.map α.unop) C
  map_id n := by rw [unop_id, CategoryTheory.Functor.map_id, equivalenceDiagramReindex_id]
  map_comp α β := by
    rw [unop_comp, CategoryTheory.Functor.map_comp, equivalenceDiagramReindex_comp]

/-- 概要：定数図式の包含は全ての単体次数について自然。
方針：任意の添字制限での定数図式の式を適用する。
規約：評価の零頂点の自然性は仮定しない。使われ方：弱同値な行から対角比較への移送。 -/
def constantEquivalenceDiagramNat (C : SSet.{u}) :
    (Functor.const SimplexCategoryᵒᵖ).obj C ⟶ simplicialEquivalenceDiagrams C where
  app n := equivalenceDiagramConstant (stdSimplex.obj n.unop) C
  naturality {n m} α := by
    change 𝟙 C ≫ _ = _
    exact (Category.id_comp _).trans
      (equivalenceDiagramConstant_reindex (stdSimplex.map α.unop) C).symm

end SerrePositivity.KST.SConstruction
