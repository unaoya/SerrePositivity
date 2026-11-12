module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AsSmallComma
public import SerrePositivity.EInfinity.FrameHom.NerveAsSmall
public import SerrePositivity.EInfinity.FrameHom.NerveEquivalenceImage

/-!
# 同じ宇宙へ持ち上げた関手の全 comma 圏の可縮性

概要：元の comma 圏の可縮性を AsSmall の関手の同じ終射へ移す。
方針：元の nerve の ULift 比較と comma の実際の圏同値を合成する。
規約：終点も同じ元の対象の up として保持する。
使われ方：分解図式への F1b の Quillen A の適用。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v u' v' w

namespace SerrePositivity.EInfinity.FrameHom.AsSmallComma

open CategoryTheory
open SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (d : D)

/-- 概要：同じ関手の AsSmall 後の comma 圏も可縮（Low 命題 3.6）。
方針：元の comma の終射の反転性を宇宙比較と元の圏同値で移す。
規約：全ての元の対象・射を保持し、単体集合モデルを要求しない。
使われ方：通常の comma と小圏の native な slice の接続。 -/
lemma terminal_localized_isIso
    (h : IsIso (AnodyneHomotopy.anodyneQ.map (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow F d))))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AsSmallComma.smallFunctor.{u, v, u', v', w} F) (AsSmall.up.obj d))))) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AsSmallComma.equivalence.{u, v, u', v', w} F d
  have : IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap e.functor)) :=
    inferInstanceAs (IsIso (NerveEquivalenceImage.imageIso e AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)).hom)
  have : IsIso (AnodyneHomotopy.anodyneQ.map (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (AsSmall.{max w u v u' v'} (CostructuredArrow F d))))) :=
    NerveAsSmall.terminal_localized_isIso _ h
  have he : nerveMap e.functor ≫ SSet.stdSimplex.isTerminalObj₀.from
      (nerve (AsSmall.{max w u v u' v'} (CostructuredArrow F d))) =
      SSet.stdSimplex.isTerminalObj₀.from
        (nerve (CostructuredArrow (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AsSmallComma.smallFunctor.{u, v, u', v', w} F) (AsSmall.up.obj d))) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [← he, CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.EInfinity.FrameHom.AsSmallComma
