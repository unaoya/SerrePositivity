module

public import SerrePositivity.EInfinity.Hammock.UnmarkedColumnLift

/-!
# 任意の添字圏上の固定列の因子化と再添字

概要：元の固定列の自然な因子化を任意の図式に制限し、前合成との両立を証明する。
方針：元の全縦射の自然性をそのまま制限する。
規約：再添字しても同じ生成矢・同じ全射を保持する。
使われ方：単体作用素と全行の分割の整合。
-/

@[expose] public section
universe u v uI vI uJ vJ
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.ColumnCut
open CategoryTheory SimplicialLocalization SimplicialLocalization.GeneratorWord

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (w : Word)
  (X Y : Paths C) (i : Fin w.length) (a : Quiver.Total C)
  {I : Type uI} [Category.{vI} I]

def sourceDiagram (F : I ⥤ ColumnCut W w X Y i a) : I ⥤ Paths C :=
  F ⋙ sourceEvaluation W w X Y i a

def targetDiagram (F : I ⥤ ColumnCut W w X Y i a) : I ⥤ Paths C :=
  F ⋙ targetEvaluation W w X Y i a

def prefixDiagram (F : I ⥤ ColumnCut W w X Y i a) : sourceDiagram W w X Y i a F ⟶
    (Functor.const I).obj (show Paths C from a.left) where
  app j := (F.obj j).cut.left
  naturality _ _ f := (prefixMap W w X Y i a).naturality (F.map f)

def residualDiagram (F : I ⥤ ColumnCut W w X Y i a) :
    (Functor.const I).obj (show Paths C from a.right) ⟶ targetDiagram W w X Y i a F where
  app j := (F.obj j).cut.right
  naturality _ _ f := (residualMap W w X Y i a).naturality (F.map f)

def generatorDiagram (_F : I ⥤ ColumnCut W w X Y i a) :
    (Functor.const I).obj (show Paths C from a.left) ⟶
      (Functor.const I).obj (show Paths C from a.right) :=
  (Functor.const I).map a.hom.toPath

def columnDiagram (F : I ⥤ ColumnCut W w X Y i a) :
    sourceDiagram W w X Y i a F ⟶ targetDiagram W w X Y i a F where
  app j := (F.obj j).row.arrow i
  naturality _ _ f := (columnMap W w X Y i a).naturality (F.map f)

lemma diagram_factorization (F : I ⥤ ColumnCut W w X Y i a) :
    prefixDiagram W w X Y i a F ≫ generatorDiagram W w X Y i a F ≫
      residualDiagram W w X Y i a F = columnDiagram W w X Y i a F := by
  apply NatTrans.ext
  funext j
  exact (F.obj j).cut.factorization.symm

variable {J : Type uJ} [Category.{vJ} J]

lemma sourceDiagram_precomp (K : J ⥤ I) (F : I ⥤ ColumnCut W w X Y i a) :
    sourceDiagram W w X Y i a (K ⋙ F) = K ⋙ sourceDiagram W w X Y i a F := rfl

lemma targetDiagram_precomp (K : J ⥤ I) (F : I ⥤ ColumnCut W w X Y i a) :
    targetDiagram W w X Y i a (K ⋙ F) = K ⋙ targetDiagram W w X Y i a F := rfl

lemma prefixDiagram_precomp (K : J ⥤ I) (F : I ⥤ ColumnCut W w X Y i a) :
    prefixDiagram W w X Y i a (K ⋙ F) =
      Functor.whiskerLeft K (prefixDiagram W w X Y i a F) := rfl

lemma residualDiagram_precomp (K : J ⥤ I) (F : I ⥤ ColumnCut W w X Y i a) :
    residualDiagram W w X Y i a (K ⋙ F) =
      Functor.whiskerLeft K (residualDiagram W w X Y i a F) := rfl

lemma generatorDiagram_precomp (K : J ⥤ I) (F : I ⥤ ColumnCut W w X Y i a) :
    generatorDiagram W w X Y i a (K ⋙ F) =
      Functor.whiskerLeft K (generatorDiagram W w X Y i a F) := rfl

lemma columnDiagram_precomp (K : J ⥤ I) (F : I ⥤ ColumnCut W w X Y i a) :
    columnDiagram W w X Y i a (K ⋙ F) =
      Functor.whiskerLeft K (columnDiagram W w X Y i a F) := rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.ColumnCut
