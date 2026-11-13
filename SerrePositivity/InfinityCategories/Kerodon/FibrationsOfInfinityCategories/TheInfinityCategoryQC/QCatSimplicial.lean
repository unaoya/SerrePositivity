module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreProduct
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：小さな quasicategory の単体的圏。
方針：内部 Hom による豊穣構造を core 関手で移送する。
規約：通常の射は単体集合の射のまま、豊穣 Hom は関手単体集合の core。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、Cat_∞ の coherent nerve の入力。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：小さな quasicategory を束縛した対象。
方針：単体集合と quasicategory 性をまとめる。
規約：単体の宇宙は u、対象の宇宙は u+1。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、単体的圏 QCat の対象。 -/
@[kerodon 020K]
structure QuasicategoryObject where
  /-- 対象の単体集合。 -/
  obj : SSet.{u}
  /-- 内ホーンの充填性。 -/
  isQuasicategory : Quasicategory obj

attribute [instance] QuasicategoryObject.isQuasicategory

/-- 概要：小さな quasicategory と単体集合の射は通常の圏をなす。
方針：単体集合の圏の恒等・合成・圏の法則を継承する。
規約：射を関手同型で商にしない。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、豊穣圏の通常の射との対応。 -/
instance quasicategoryObject_category : Category.{u} QuasicategoryObject.{u} where
  Hom X Y := X.obj ⟶ Y.obj
  id X := 𝟙 X.obj
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- 概要：quasicategory の通常の圏を内部 Hom で豊穣化する。
方針：閉モノイダル圏の自己豊穣の合成と単位を使う。
規約：この段階の Hom は core を取る前の関手単体集合。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、core による豊穣構造の移送元。 -/
@[kerodon 020K]
instance quasicategoryObject_enrichedCategory : EnrichedCategory SSet.{u} QuasicategoryObject.{u} where
  Hom X Y := (ihom X.obj).obj Y.obj
  id X := MonoidalClosed.id X.obj
  comp X Y Z := MonoidalClosed.comp X.obj Y.obj Z.obj
  id_comp X Y := MonoidalClosed.id_comp X.obj Y.obj
  comp_id X Y := MonoidalClosed.comp_id X.obj Y.obj
  assoc W X Y Z := MonoidalClosed.assoc W.obj X.obj Y.obj Z.obj

/-- 概要：内部 Hom の豊穣構造の零単体は通常の関手と一致する。
方針：閉構造の単位からの射との同値を使う。
規約：通常の射は QuasicategoryObject の圏構造を使う。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、core 移送の通常の射の保持。 -/
@[kerodon 020K]
instance quasicategoryObject_simplicialCategory : SimplicialCategory.{u} QuasicategoryObject.{u} where
  homEquiv {X Y} := curryHomEquiv' (X := X.obj) (Y := Y.obj)
  homEquiv_id X := curry'_id X.obj
  homEquiv_comp {X Y Z} f g := curry'_comp (C := SSet.{u}) f g

/-- 概要：関手単体集合の core を Hom とする小さな quasicategory の圏。
方針：core 関手の lax monoidal 構造で豊穣 Hom と合成を移送する。
規約：対象と通常の射は QuasicategoryObject と同じ。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、Cat_∞ の定義の単体的圏 QCat。 -/
def QCat : Type (u + 1) := TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} QuasicategoryObject.{u}

/-- 概要：QCat の通常の圏構造。
方針：豊穣構造の移送が保持する通常の圏を継承する。
規約：通常の射は単体集合の射。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、coherent nerve の通常の圏の入力。 -/
instance qCat_category : Category.{u} QCat.{u} :=
  inferInstanceAs (Category.{u}
    (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} QuasicategoryObject.{u}))

/-- 概要：QCat は core を豊穣 Hom に持つ単体的圏。
方針：単位からの射の同値で通常の射を保って豊穣構造を移送する。
規約：FunctorIso の類ではなく実際の core 単体集合を使う。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、Cat_∞ の coherent nerve。 -/
noncomputable instance qCat_simplicialCategory : SimplicialCategory QCat.{u} :=
  TransportEnrichment.enrichedOrdinaryCategory QuasicategoryObject.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u}
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv_eq

/-- 概要：QCat の豊穣 Hom は関手単体集合の core に一致する。
方針：豊穣構造の移送の Hom の定義を計算する。
規約：対象 X、Y は同じ宇宙の小さな quasicategory。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、豊穣 Hom の具体的な表示。 -/
lemma qCat_sHom (X Y : QCat.{u}) :
    SimplicialCategory.sHom X Y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom X.obj).obj Y.obj) : SSet.{u}) := rfl

/-- 概要：QCat の全ての豊穣 Hom は Kan 複体。
方針：関手単体集合の quasicategory 性と core の Kan 性を使う。
規約：Hom に追加の充填仮定を置かない。
使われ方：Kerodon Proposition 5.5.3.3（Tag 020B）、γ1 の局所 Kan 性の仮定。 -/
@[kerodon 020B]
instance qCat_sHom_kanComplex (X Y : QCat.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := by
  rw [qCat_sHom]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "2.4.2.7" (partial := component) "仮定：小さい準圏と、関手単体集合の core で豊穣化した単体圏（HA の最初の模型と一致）。結論：写像空間が Kan であり、その単体圏の nerve が Cat∞ を与える部分に一致。位相実現の nerve との比較と反対圏の対称モノイダル構造は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_sHom_kanComplex
attribute [cite HTT "3.0.0.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat
attribute [cite HTT "3.0.0.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_sHom
attribute [cite HTT "3.0.0.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat
attribute [cite HTT "3.0.0.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_category
attribute [cite HTT "3.0.0.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_simplicialCategory
attribute [cite HTT "3.0.0.3"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_sHom_kanComplex
attribute [cite HTT "3.0.0.4"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCat_sHom
