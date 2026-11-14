module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CommaComparisons.CommaPreLeftRetraction
public import SerrePositivity.EInfinity.FrameHom.NerveQuillenA
public import SerrePositivity.EInfinity.FrameHom.CofinalAnodyneImage
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy

/-!
# 元の左変数の余終性から全図式の比較の余終性

概要：Low 命題 3.7 の全図式の左変数の比較の nerve を反転する。
方針：各 comma の元の切断と収縮により、分解側の弱可縮な comma へ移す。
規約：元の比較射の全対象・全射を保持し、モデル構造を要求しない。
使われ方：固定右脚ごとの比較を全右脚の図式へ接続する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.FrameHom.CommaPreLeft

open CategoryTheory
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

variable {K L C J : Type u} [Category.{u} K] [Category.{u} L]
  [Category.{u} C] [Category.{u} J]
  (P : K ⥤ L) (Q : L ⥤ C) (R : J ⥤ C)

/-- 概要：全図式の comma の元の射影は anodyne 反転後に可逆（Low 命題 3.7）。
方針：元の切断と自然変換の全次数の nerve のホモトピーから両逆を得る。
規約：元の射影の nerve そのものを反転する。
使われ方：既知の分解の comma の弱可縮性への帰着。 -/
lemma projection_localized_isIso (T : Comma Q R) :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaPreLeftRetraction.projection P Q R T))) := by
  have hs : nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaPreLeftRetraction.canonicalSection P Q R T) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaPreLeftRetraction.projection P Q R T) = 𝟙 _ := by
    change nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaPreLeftRetraction.canonicalSection P Q R T ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaPreLeftRetraction.projection P Q R T) = 𝟙 _
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaPreLeftRetraction.canonicalSection_projection]
    rfl
  exact (AnodyneHomotopy.mapRetractionIso AnodyneHomotopy.anodyneQ
    (Localization.inverts _ SSet.anodyneExtensions) (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaPreLeftRetraction.projection P Q R T))
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaPreLeftRetraction.canonicalSection P Q R T)) hs
    (NerveHomotopy.homotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaPreLeftRetraction.contraction P Q R T))).isIso_hom

/-- 概要：元の左変数の余終性は全図式の比較に保たれる（Low 命題 3.7）。
方針：元の各 comma の収縮先の弱可縮性を Quillen A で全体へ移す。
規約：成分の余終性から全体の結論を省略せず、各 comma の収縮を使う。
使われ方：三本矢の全図式への分解側の比較。 -/
lemma comparison_isLeftCofinal (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap P)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap (Comma.preLeft P Q R)) := by
  apply NerveQuillenA.nerveMap_isLeftCofinal_of_weaklyContractible_comma
  intro T
  exact (AnodyneWeakDetection.isWeakHomotopyEquivalence (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaPreLeftRetraction.projection P Q R T))
    (projection_localized_isIso P Q R T)).weaklyContractible_iff.mpr
      (NerveQuillenA.comma_isWeaklyContractible P hP T.left)

/-- 概要：元の全図式の同じ比較は anodyne 反転後に可逆（Low 命題 3.7）。
方針：元の比較の全 comma による余終性を同じ射の反転性へ移す。
規約：元の両端の nerve に Kan 性を要求しない。
使われ方：元の全右脚の Grothendieck 図式の比較の反転。 -/
lemma comparison_localized_isIso (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap P)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (Comma.preLeft P Q R))) :=
  leftCofinal_localized_isIso _ (comparison_isLeftCofinal P Q R hP)

end SerrePositivity.EInfinity.FrameHom.CommaPreLeft
