module

public import SerrePositivity.EInfinity.Hammock.UnmarkedFixedColumn

/-!
# 元の列の固定生成矢を挟む自然な因子化

概要：元の列の自然変換を、指定接頭列・同じ生成矢・残りの自然変換へ厳密に分ける。
方針：元の全縦射の正方形を FixedCut.square で分解する。
規約：追加の自然性を入力とせず、元の列への因子化式を証明する。
使われ方：全行の接頭列と残りの実際の図式。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.ColumnCut
open CategoryTheory SimplicialLocalization SimplicialLocalization.GeneratorWord

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (w : Word)
  (X Y : Paths C) (i : Fin w.length) (a : Quiver.Total C)

def prefixMap : sourceEvaluation W w X Y i a ⟶
    (Functor.const (ColumnCut W w X Y i a)).obj (show Paths C from a.left) where
  app P := P.cut.left
  naturality P Q f := by
    change (f.app (w.source i)).comp Q.cut.left = P.cut.left.comp Quiver.Path.nil
    simpa only [Quiver.Path.comp_nil] using (FixedCut.square W P.cut Q.cut
      (f.app (w.source i)) (f.app (w.target i)) (f.app_mem (w.source i)) (f.comm i)).1.symm

def residualMap :
    (Functor.const (ColumnCut W w X Y i a)).obj (show Paths C from a.right) ⟶
      targetEvaluation W w X Y i a where
  app P := P.cut.right
  naturality P Q f := by
    change Quiver.Path.nil.comp Q.cut.right = P.cut.right.comp (f.app (w.target i))
    simpa only [Quiver.Path.nil_comp] using (FixedCut.square W P.cut Q.cut
      (f.app (w.source i)) (f.app (w.target i)) (f.app_mem (w.source i)) (f.comm i)).2.symm

def generatorMap :
    (Functor.const (ColumnCut W w X Y i a)).obj (show Paths C from a.left) ⟶
      (Functor.const (ColumnCut W w X Y i a)).obj (show Paths C from a.right) :=
  (Functor.const (ColumnCut W w X Y i a)).map a.hom.toPath

def columnMap : sourceEvaluation W w X Y i a ⟶ targetEvaluation W w X Y i a where
  app P := P.row.arrow i
  naturality _ _ f := (f.comm i).symm

lemma prefixMap_mem (P : ColumnCut W w X Y i a) :
    W.paths ((prefixMap W w X Y i a).app P) := P.cut.left_mem

lemma columnMap_factorization : prefixMap W w X Y i a ≫ generatorMap W w X Y i a ≫
    residualMap W w X Y i a = columnMap W w X Y i a := by
  apply NatTrans.ext
  funext P
  exact P.cut.factorization.symm

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.ColumnCut
