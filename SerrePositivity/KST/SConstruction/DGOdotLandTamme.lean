module
public import SerrePositivity.KST.SConstruction.DGOdotCatPerfInput
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientValuePullback

/-!
概要：d の実商列と c の同じ ⊙ から LT の Cat^perf 版の形式的結論を導く。
方針：Tamme の元の両射影を保つ分裂と既存の Verdier 列消去を特殊化する。
規約：d は明示入力。四完備性の標準証人は D から供給する。K の局所化性は主張しない。
使われ方：供給後も同じ四辺・実 cospan・極限錐を保持する LT 接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra InfinityCategories LocalizingInvariants

open scoped Simplicial
local instance landTammeSpectrum_simplicialCategory : SimplicialCategory OmegaSpectrum.{u + 1} :=
  OmegaSpectrum.simplicialCategory
namespace DGOdotCatPerfInput
variable {R : Type u} [CommRing R] {d : DGOdotInput R}
  (c : DGOdotCatPerfInput R d) (h : DGOdotLaxVerdierInput R d)
  {F : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}} (hF : IsPerfectLocalizingInvariant F)

local notation "Q" => c.perfectQuotient h

/-- 概要：元の四つの BF 射を持つ LT の実正方形。
方針：同じ Cat^perf の商入力へ既存の二脚の構成を適用する。
規約：終点は c の実 ⊙。使われ方：全局所化不変量での切除。 -/
def landTammeSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ Sp.{u + 1} :=
  (Q).valuePullbackSquare hF

/-- 概要：d の入力を仮定した LT の Cat^perf 版の結論。
方針：同じ Tamme 分裂と実 Verdier 列の消去を使う。
規約：未供給入力を除去しない。使われ方：具体的供給後の主定理。 -/
theorem landTamme_isPullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (c.landTammeSquare h hF) :=
  (Q).valuePullbackSquare_isPullback hF

/-- 概要：LT の下辺は元の C への値の同じ BF 射。
方針：四辺固定の既存構成を読む。規約：射の類だけで代用しない。
使われ方：元の完全射との照合。 -/
lemma landTamme_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ c.landTammeSquare h hF =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((Q).valueCSource F)).edge :=
  (Q).valuePullbackSquare_bottom hF

/-- 概要：LT の左辺は元の D への値の同じ BF 射。
方針：既存の境界固定を保持する。規約：新しい脚を選ばない。
使われ方：元の二射影の回収。 -/
lemma landTamme_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ c.landTammeSquare h hF =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((Q).valueDSource F)).edge :=
  (Q).valuePullbackSquare_left hF

/-- 概要：LT の右辺は元の C から同じ実 ⊙ への脚の値。
方針：同じ完備化射を通す。規約：完備化後の射を厳密商と仮定しない。
使われ方：⊙ を終点とする主定理の右辺。 -/
lemma landTamme_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ c.landTammeSquare h hF =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((Q).valueCLeg F)).edge :=
  (Q).valuePullbackSquare_right hF

/-- 概要：LT の上辺は元の D から同じ実 ⊙ への脚の値。
方針：同じ Morita 逆を用いる脚を保持する。規約：任意の完備化へ置換しない。
使われ方：二脚の実 cospan の回収。 -/
lemma landTamme_top : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ c.landTammeSquare h hF =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((Q).valueDLeg F)).edge :=
  (Q).valuePullbackSquare_top hF

/-- 概要：正方形の左下は元の対角始域の同じ不変量値。
方針：BF 表示と元の Sp 頂点を既存比較で同定する。
規約：同値な別頂点への言い換えではない。使われ方：元の値の極限錐。 -/
lemma landTamme_source : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (c.landTammeSquare h hF) 0 0 =
    F.app (Opposite.op ⦋0⦌) (perfectStableVertex
      (dgKInputStableValue R (dgOdotDiagonalSourceInput R d)) c.source_complete) :=
  (Q).valuePullbackSquare_vertex_value hF

/-- 概要：右上は c の同じ実 ⊙ の不変量値。
方針：元の上辺の終点と BF 表示を照合する。規約：商候補へ置換しない。
使われ方：LT の終点の回収。 -/
lemma landTamme_odot : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (c.landTammeSquare h hF) 1 1 =
    F.app (Opposite.op ⦋0⦌) (perfectStableVertex
      (dgKInputStableValue R (dgOdotAlgebraInput R d)) c.odot_complete) := by
  exact (NativeSquareRows.vertex11 _ _ (c.landTamme_top h hF)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _)

/-- 概要：右下は元の左代数の同じ不変量値。方針：元の下辺の終点を読む。
規約：BF 表示の別対象に留めない。使われ方：四頂点の回収。 -/
lemma landTamme_leftValue : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (c.landTammeSquare h hF) 1 0 =
    F.app (Opposite.op ⦋0⦌) (perfectStableVertex
      (dgKInputStableValue R (dgOdotLeftInput R d)) c.left_complete) :=
  (NativeSquareRows.vertex10 _ _ (c.landTamme_bottom h hF)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _)

/-- 概要：左上は元の右代数の同じ不変量値。方針：元の上辺の始点を読む。
規約：入力した右代数を保つ。使われ方：四頂点の回収。 -/
lemma landTamme_rightValue : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (c.landTammeSquare h hF) 0 1 =
    F.app (Opposite.op ⦋0⦌) (perfectStableVertex
      (dgKInputStableValue R (dgOdotRightInput R d)) c.right_complete) :=
  (NativeSquareRows.vertex01 _ _ (c.landTamme_top h hF)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _)

/-- 概要：元の同じ二脚からなる LT の実 cospan。
方針：四辺を固定した正方形の境界を取る。規約：値を定義し直さない。
使われ方：主定理の極限図式。 -/
def landTammeCospan : (horn 2 2 : SSet.{u + 2}) ⟶ Sp.{u + 1} :=
  (Q).valuePullbackCospan hF

/-- 概要：元の対角始域の値を頂点とする実錐。
方針：同じ正方形から既存の錐を取る。規約：候補錐の極限性は次で証明する。
使われ方：LT の Cat^perf 版の実極限結論。 -/
def landTammeCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (c.landTammeCospan h hF) := (Q).valuePullbackCone hF

/-- 概要：元の二脚と同じ頂点を持つ LT の錐は極限。
方針：同じ正方形の pullback 性を使う。規約：π 群の比較だけではない。
使われ方：供給後の主定理の錐版。 -/
theorem landTammeCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (c.landTammeCone h hF) :=
  (Q).valuePullbackCone_isLimit hF

/-- 概要：極限錐の頂点は元の始域の不変量値そのもの。
方針：既存の頂点回収を使う。規約：頂点の選択を変更しない。
使われ方：元の dg 四角形からの値の比較。 -/
lemma landTammeCone_source : (c.landTammeCone h hF).vertex =
    F.app (Opposite.op ⦋0⦌) (perfectStableVertex
      (dgKInputStableValue R (dgOdotDiagonalSourceInput R d)) c.source_complete) :=
  (Q).valuePullbackCone_vertex_value hF

/-- 概要：Tamme 分裂は元の二射影を順方向に持つ同じ積同値。
方針：既存の両射影同値を同じ二入力へ適用する。
規約：半直交分解の圏自体を積と同定しない。使われ方：LT の分裂部分の公開出力。 -/
def tammeProjectionEquivalence :=
  hF.tammePerfectProjectionEquivalence (dgOdotLowerExactMap R d)
    (dgOdotUpperExactMap R d) c.left_complete c.right_complete

/-- 概要：元の商を完備化した右射の二脚は、同じ LT の二脚を回収する。
方針：一般商の脚と完備化後の脚の既存比較を使う。
規約：元の suspension 自然性を保持する。使われ方：d の射影との接続。 -/
def landTammeCLeg_comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (Q).cLeg.hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)
      (Q).sequence.projection).hom := (Q).cLeg_projectionIso

/-- 概要：D 側の脚も元の完備化後の射影の脚を保持する。
方針：元の定義の厳密回収を使う。規約：符号・向きを変えない。
使われ方：同じ右射の二脚への整合。 -/
lemma landTammeDLeg_comparison : (Q).dLeg = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg
    (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d) (Q).sequence.projection :=
  (Q).dLeg_projection_eq

/-- 概要：元の C への射は d の包含と同じ第一射影の合成。
方針：固定した商入力の定義を読む。規約：新しい左脚を置かない。
使われ方：元の dg 二射影との接続。 -/
lemma landTamme_cSource_original : (Q).cSource.hom =
    h.inclusion.hom ≫ (laxFst (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom := rfl

/-- 概要：元の D への射は同じ第二射影の合成。
方針：固定した入力を保持する。規約：同値先の任意の射を使わない。
使われ方：元の右射影との接続。 -/
lemma landTamme_dSource_original : (Q).dSource.hom =
    h.inclusion.hom ≫ (laxSnd (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom := rfl

/-- 概要：C 脚は d の元の商射の脚と c の同じ Morita 逆の合成。
方針：完備化の指定を展開する。規約：元の商射を保つ。
使われ方：実 ⊙ への C 脚の照合。 -/
lemma landTamme_cLeg_original : (Q).cLeg.hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)
      h.projection).hom ≫ (dgOdotQuotientCompletion R d).hom := rfl

/-- 概要：D 脚も元の商射の脚と同じ Morita 逆の合成。
方針：実完備化射の指定を保持する。規約：逆射を選び直さない。
使われ方：実 ⊙ への D 脚の照合。 -/
lemma landTamme_dLeg_original : (Q).dLeg.hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientDLeg (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)
      h.projection).hom ≫ (dgOdotQuotientCompletion R d).hom := rfl

/-- 概要：実 cospan の C 側は同じ C 脚の BF 値。
方針：元の境界の式を使う。規約：図式の射を置換しない。
使われ方：極限錐の脚の回収。 -/
lemma landTammeCospan_C : horn₂₂.ι₀₂ ≫ c.landTammeCospan h hF =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((Q).valueCLeg F)).edge :=
  (Q).valuePullbackCospan_C hF

/-- 概要：実 cospan の D 側は同じ D 脚の BF 値。
方針：元の上辺を保持する。規約：元の二脚の順序を保つ。
使われ方：LT の同じ極限図式。 -/
lemma landTammeCospan_D : horn₂₂.ι₁₂ ≫ c.landTammeCospan h hF =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((Q).valueDLeg F)).edge :=
  (Q).valuePullbackCospan_D hF

/-- 概要：Tamme 同値の第一射影は同じ元の第一射影の値。
方針：既存の両射影を保つ比較を使う。規約：新しい積同値を選ばない。
使われ方：分裂と LT の下辺の整合。 -/
lemma tammeProjectionEquivalence_fst : (c.tammeProjectionEquivalence hF).hom ≫
    SpectrumHo.hom (Binary.fst _ _) =
      perfectInvariantSpectrumHom F (laxFst (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d))
        (perfectLaxCategory_isIdempotentComplete (dgOdotLowerExactMap R d)
          (dgOdotUpperExactMap R d) c.left_complete c.right_complete) c.left_complete :=
  hF.tammePerfectProjectionEquivalence_fst _ _ _ _

/-- 概要：Tamme 同値の第二射影も同じ元の射影の値。
方針：既存の第二射影の式を適用する。規約：積因子を入れ替えない。
使われ方：分裂と LT の左辺の整合。 -/
lemma tammeProjectionEquivalence_snd : (c.tammeProjectionEquivalence hF).hom ≫
    SpectrumHo.hom (Binary.snd _ _) =
      perfectInvariantSpectrumHom F (laxSnd (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d))
        (perfectLaxCategory_isIdempotentComplete (dgOdotLowerExactMap R d)
          (dgOdotUpperExactMap R d) c.left_complete c.right_complete) c.right_complete :=
  hF.tammePerfectProjectionEquivalence_snd _ _ _ _

end DGOdotCatPerfInput
end SerrePositivity.KST.SConstruction
