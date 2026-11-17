module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaPreLeftCofinality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.GrothendieckConstruction.CommaGrothendieck
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.CostructuredArrowPreDiagram
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage

/-!
# 分解から全左脚への右変数の全図式の比較の反転

概要：Low 命題 3.7 の元の Grothendieck 図式の比較を anodyne 反転後に可逆とする。
方針：元の comma 表示での比較との厳密な整合と全 comma の収縮を使う。
規約：元の全図式の比較関手を保持し、単体集合モデルは要求しない。
使われ方：元の Map^h から三本矢の全図式への比較の分解側の反転性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom

open _root_.CategoryTheory
open _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel

variable {K L C J : Type u} [Category.{u} K] [Category.{u} L]
  [Category.{u} C] [Category.{u} J]
  (P : K ⥤ L) (Q : L ⥤ C) (R : J ⥤ C)

/-- 概要：元の全図式の比較は comma 表示の左変数の比較と厳密に整合（Low 命題 3.7）。
方針：全対象・全射で元の底と fiber の左成分を回収する。
規約：元の比較を別の関手へ置き換えない。
使われ方：全 comma の収縮の結果を元の Grothendieck 関手へ移す。 -/
lemma fixedRightGrothendieckComparison_toComma :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedRightGrothendieckComparison P Q R ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.toComma Q R =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.toComma (P ⋙ Q) R ⋙ Comma.preLeft P Q R := by
  refine CategoryTheory.Functor.ext (fun S => rfl) ?_
  intro S T f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply CommaMorphism.ext
  · change (𝟙 (P.obj S.fiber.left)) ≫ P.map f.fiber.left = P.map f.fiber.left
    exact Category.id_comp _
  · rfl

/-- 概要：元の右変数の全図式の比較は anodyne 反転後に可逆（Low 命題 3.7）。
方針：comma 表示の全図式の反転性と元の二つの表示同値の nerve を合成する。
規約：元の比較射の像そのものの可逆性を主張する。
使われ方：分解から全左脚への同じ全図式の比較の反転。 -/
lemma fixedRightGrothendieckComparison_localized_isIso
    (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap P)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedRightGrothendieckComparison P Q R))) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.toComma (P ⋙ Q) R))) :=
    inferInstanceAs (IsIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage.imageIso
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.equivalence (P ⋙ Q) R) AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)).hom)
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.toComma Q R))) :=
    inferInstanceAs (IsIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage.imageIso
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.equivalence Q R) AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)).hom)
  have : IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (Comma.preLeft P Q R))) :=
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaPreLeft.comparison_localized_isIso P Q R hP
  have h : nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedRightGrothendieckComparison P Q R) ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.toComma Q R) =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.toComma (P ⋙ Q) R) ≫ nerveMap (Comma.preLeft P Q R) := by
    change nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedRightGrothendieckComparison P Q R ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.toComma Q R) =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.toComma (P ⋙ Q) R ⋙ Comma.preLeft P Q R)
    rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.fixedRightGrothendieckComparison_toComma]
  have hh := congrArg AnodyneHomotopy.anodyneQ.map h
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hh
  have : IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedRightGrothendieckComparison P Q R)) ≫
      AnodyneHomotopy.anodyneQ.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.toComma Q R))) :=
    hh.symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp this

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
