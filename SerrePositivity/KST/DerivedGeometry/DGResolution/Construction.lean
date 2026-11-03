module

public import SerrePositivity.DifferentialGraded.Resolution.Cell
public import SerrePositivity.KST.DerivedGeometry.DGResolution.Filtration
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LocalFlatness

/-!
# 一般の dg 圏の生成元添加による分解

概要：任意の小さい dg 圏に、対象を保つ具体的な分解と増大関手を与える。
方針：閉元の自由被覆から境界生成元を添加する既存の逐次構成を再利用する。
規約：存在・準同値・K-flat 性を未証明フィールドとして受け取らない。
使われ方：Drinfeld Lemma 13.5・Thm 3.4、KST D4、K-L1b・L3 の商への供給。
-/

@[expose] public section
noncomputable section
universe u v

namespace SerrePositivity.KST.DerivedGeometry.DGResolution

open CategoryTheory
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/--
概要：閉元の自由被覆と境界生成元添加の余極限で構成した分解の対象型。
方針：既存の具体的な段階構成を用いる。
規約：層の圏に特殊化せず、元の Hom の平坦性・有界性を要求しない。
使われ方：Drinfeld Lemma 13.5、KST D4 の商を取る前の分解。
-/
abbrev Objects := DGCategoryCellResolution.Source A D

/--
概要：分解と元の dg 圏は同じ対象ラベルを持つ。
方針：固定対象構成のラッパーを外す同値を使う。
規約：これは対象の型の同値であり、dg 圏の同値とは区別する。
使われ方：Drinfeld Lemma 13.5 の対象固定条件。
-/
def objectEquiv : D ≃ Objects A D := (DGCategoryCellResolution.candidate A D).objectEquiv

/--
概要：生成元添加の極限から元の dg 圏への増大関手。
方針：段階ごとの増大関手を余極限から降ろした既存の構成を使う。
規約：対象は元のラベルへ戻す。
使われ方：Drinfeld Lemma 13.5、KST D4 の準同値による移送。
-/
def augmentation : DGFunctor A (Objects A D) D := DGCategoryCellResolution.augmentation A D

/--
概要：増大関手は各対象を元のラベルへ送る。
方針：具体的構成の定義を展開する。
規約：対象の持ち上げに選択を使わない。
使われ方：Drinfeld Lemma 13.5 の対象固定性。
-/
lemma augmentation_object (x : D) : (augmentation A D).obj (objectEquiv A D x) = x := rfl

/--
概要：分解の全 Hom 複体は非有界な意味で K-flat。
方針：生成元の語長フィルトレーション、短完全列、二重の逐次余極限の既存証明を使う。
規約：次数ごとの自由性だけで非有界 K-flat 性を結論しない。
使われ方：Drinfeld Thm 3.4 の片側 K-flat 条件、KST D4 の導来商。
-/
theorem homKFlat (x y : Objects A D) : complexKFlat A (homObject A (Objects A D) x y) :=
  limitHom_kFlat A D x.val y.val

/--
概要：増大関手は全 Hom で準同型を誘導する。
方針：各有限段階の境界充填を余極限へ渡した既存証明を用いる。
規約：準同型性を入力として要求しない。
使われ方：Drinfeld Lemma 13.5 の分解の比較。
-/
theorem augmentation_homQuasiIso : HomQuasiIso (augmentation A D) :=
  DGCategoryCellResolution.augmentation_homQuasiIso A D

/--
概要：具体的増大関手は dg 準同値である。
方針：境界充填による Hom 準同型性と対象固定性を使う。
規約：元の Hom の平坦性は要求しない。
使われ方：Drinfeld Lemma 13.5、KST D4 の H⁰ の移送。
-/
theorem augmentation_quasiEquivalence : QuasiEquivalence (augmentation A D) :=
  DGCategoryCellResolution.augmentation_quasiEquivalence A D

/--
概要：分解の増大関手は H⁰ 上の圏同値を与える。
方針：Hom 準同型から完全忠実性を得て、対象固定性から本質的全射性を得る。
規約：前三角化との両立は別の証明で与える。
使われ方：Drinfeld Lemma 13.5、KST D4 の導来比較の前段階。
-/
instance augmentation_homotopy_isEquivalence : (augmentation A D).onHomotopy.IsEquivalence := by
  let h := augmentation_quasiEquivalence A D
  let : (augmentation A D).onHomotopy.Full :=
    (augmentation A D).onHomotopy_full_of_homQuasiIso h.1
  let : (augmentation A D).onHomotopy.Faithful :=
    (augmentation A D).onHomotopy_faithful_of_homQuasiIso h.1
  let : (augmentation A D).onHomotopy.EssSurj := h.2
  exact { }

/--
概要：分解後は任意の収縮対象集合について商の片側 K-flat 条件を満たす。
方針：全 Hom の K-flat 性を殺す対象へ入る Hom に制限する。
規約：既存 localKFlat の定義を変更しない。
使われ方：Drinfeld Thm 3.4、既存 localPerfectQuotientEquivalence への入力。
-/
theorem localKFlat (N : Set (Objects A D)) : DGQuotient.localKFlat A (Objects A D) N :=
  DGQuotient.allHomKFlat_local A (Objects A D) (homKFlat A D) N

end SerrePositivity.KST.DerivedGeometry.DGResolution
