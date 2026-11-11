module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnLift

/-!
# 任意の添字圏上の固定列の因子化と再添字

概要：元の固定列の自然な因子化を任意の図式に制限し、前合成との両立を証明する。
方針：元の全縦射の自然性をそのまま制限する。
規約：再添字しても同じ生成矢・同じ全射を保持する。
使われ方：単体作用素と全行の分割の整合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uI vI uJ vJ
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
  (X Y : Paths C) (i : Fin w.length) (a : Quiver.Total C)
  {I : Type uI} [Category.{vI} I]

def sourceDiagram (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) : I ⥤ Paths C :=
  F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut.sourceEvaluation W w X Y i a

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization (sourceDiagram)


def targetDiagram (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) : I ⥤ Paths C :=
  F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut.targetEvaluation W w X Y i a

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization (targetDiagram)


def prefixDiagram (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) : sourceDiagram W w X Y i a F ⟶
    (Functor.const I).obj (show Paths C from a.left) where
  app j := (F.obj j).cut.left
  naturality _ _ f := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedColumnFactorization.prefixMap W w X Y i a).naturality (F.map f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization (prefixDiagram)


def residualDiagram (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) :
    (Functor.const I).obj (show Paths C from a.right) ⟶ targetDiagram W w X Y i a F where
  app j := (F.obj j).cut.right
  naturality _ _ f := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedColumnFactorization.residualMap W w X Y i a).naturality (F.map f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization (residualDiagram)


def generatorDiagram (_F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) :
    (Functor.const I).obj (show Paths C from a.left) ⟶
      (Functor.const I).obj (show Paths C from a.right) :=
  (Functor.const I).map a.hom.toPath

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization (generatorDiagram)


def columnDiagram (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) :
    sourceDiagram W w X Y i a F ⟶ targetDiagram W w X Y i a F where
  app j := (F.obj j).row.arrow i
  naturality _ _ f := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedColumnFactorization.columnMap W w X Y i a).naturality (F.map f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization (columnDiagram)


lemma diagram_factorization (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.prefixDiagram W w X Y i a F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.generatorDiagram W w X Y i a F ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.residualDiagram W w X Y i a F = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.columnDiagram W w X Y i a F := by
  apply NatTrans.ext
  funext j
  exact (F.obj j).cut.factorization.symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization (diagram_factorization)


variable {J : Type uJ} [Category.{vJ} J]

lemma sourceDiagram_precomp (K : J ⥤ I) (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) :
    sourceDiagram W w X Y i a (K ⋙ F) = K ⋙ sourceDiagram W w X Y i a F := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization (sourceDiagram_precomp)


lemma targetDiagram_precomp (K : J ⥤ I) (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) :
    targetDiagram W w X Y i a (K ⋙ F) = K ⋙ targetDiagram W w X Y i a F := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization (targetDiagram_precomp)


lemma prefixDiagram_precomp (K : J ⥤ I) (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.prefixDiagram W w X Y i a (K ⋙ F) =
      Functor.whiskerLeft K (prefixDiagram W w X Y i a F) := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization (prefixDiagram_precomp)


lemma residualDiagram_precomp (K : J ⥤ I) (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.residualDiagram W w X Y i a (K ⋙ F) =
      Functor.whiskerLeft K (residualDiagram W w X Y i a F) := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization (residualDiagram_precomp)


lemma generatorDiagram_precomp (K : J ⥤ I) (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.generatorDiagram W w X Y i a (K ⋙ F) =
      Functor.whiskerLeft K (generatorDiagram W w X Y i a F) := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization (generatorDiagram_precomp)


lemma columnDiagram_precomp (K : J ⥤ I) (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.columnDiagram W w X Y i a (K ⋙ F) =
      Functor.whiskerLeft K (columnDiagram W w X Y i a F) := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization (columnDiagram_precomp)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization
