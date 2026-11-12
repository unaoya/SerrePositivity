module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：coherent nerve による ∞ 圏の ∞ 圏と空間の ∞ 圏。
方針：局所 Kan な QCat と Kan 複体の単体的圏に γ1 を適用する。
規約：小さな対象の単体は宇宙 u、coherent nerve は宇宙 u+1。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、Construction 3.1.6.1（Tag 00TZ）、F1c と F1d の値域。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：小さな quasicategory の ∞ 圏 Cat_∞。
方針：関手単体集合の core を Hom とする単体的圏 QCat の coherent nerve を取る。
規約：対象が宇宙 u+1 に属するので値も SSet.{u+1}。
使われ方：Kerodon Construction 5.5.3.1（Tag 0209）、straightening の Cat_∞ 値関手の標的。 -/
@[kerodon 020T, kerodon 020U]
noncomputable def CatInfinity : SSet.{u + 1} := SimplicialNerve _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}

/-- 概要：Cat_∞ は quasicategory。
方針：QCat の局所 Kan 性から既存の γ1 の定理を適用する。
規約：coherent nerve の追加の充填仮定は置かない。
使われ方：Kerodon Proposition 5.5.3.3（Tag 020B）、Cat_∞ 値の関手 ∞ 圏。 -/
@[kerodon 020B, kerodon 020U, kerodon 04FD]
instance catInfinity_quasicategory : Quasicategory CatInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}

/-- 概要：Cat_∞ 値の関手 ∞ 圏。
方針：単体集合の内部 Hom を使う。
規約：定義域 C は値域と同じ宇宙 u+1 に配置する。
使われ方：Kerodon §5.5（Tag 01YV）、§5.6（Tag 027M）、straightening の関手側の対象。 -/
noncomputable def CatInfinityFunctor (C : SSet.{u + 1}) : SSet.{u + 1} := (ihom C).obj CatInfinity.{u}

/-- 概要：Cat_∞ 値の関手単体集合は quasicategory。
方針：内部 Hom が quasicategory 性を保つことを使う。
規約：定義域 C の quasicategory 性は不要。
使われ方：Kerodon §5.5（Tag 01YV）、§5.6（Tag 027M）、straightening の関手 ∞ 圏の構成。 -/
instance catInfinityFunctor_quasicategory (C : SSet.{u + 1}) :
    Quasicategory (CatInfinityFunctor C) := inferInstanceAs (Quasicategory ((ihom C).obj CatInfinity))

/-- 概要：小さな Kan 複体を束縛した対象。
方針：単体集合と全ホーンの充填性をまとめる。
規約：単体の宇宙は u、対象の宇宙は u+1。
使われ方：Kerodon Construction 3.1.6.1（Tag 00TZ）、空間の ∞ 圏の単体的圏の対象。 -/
@[kerodon 00TZ]
structure KanObject where
  /-- 対象の単体集合。 -/
  obj : SSet.{u}
  /-- 全ホーンの充填性。 -/
  isKanComplex : KanComplex obj

attribute [instance] KanObject.isKanComplex

/-- 概要：小さな Kan 複体と単体集合の射は通常の圏をなす。
方針：単体集合の圏の恒等・合成を継承する。
規約：通常の射をホモトピーで商にしない。
使われ方：Kerodon Construction 3.1.6.1（Tag 00TZ）、Kan の豊穣構造の通常の射。 -/
instance kanObject_category : Category.{u} KanObject.{u} where
  Hom X Y := X.obj ⟶ Y.obj
  id X := 𝟙 X.obj
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- 概要：Kan 複体の圏を関手単体集合で豊穣化する。
方針：閉モノイダル構造の内部 Hom と合成を使う。
規約：豊穣 Hom は core を取る必要のない実際の内部 Hom。
使われ方：Kerodon Construction 3.1.6.1（Tag 00TZ）、空間の ∞ 圏の豊穣構造。 -/
instance kanObject_enrichedCategory : EnrichedCategory SSet.{u} KanObject.{u} where
  Hom X Y := (ihom X.obj).obj Y.obj
  id X := MonoidalClosed.id X.obj
  comp X Y Z := MonoidalClosed.comp X.obj Y.obj Z.obj
  id_comp X Y := MonoidalClosed.id_comp X.obj Y.obj
  comp_id X Y := MonoidalClosed.comp_id X.obj Y.obj
  assoc W X Y Z := MonoidalClosed.assoc W.obj X.obj Y.obj Z.obj

/-- 概要：Kan 複体の豊穣構造の零単体は通常の射と一致。
方針：内部 Hom の単位からの射との同値を使う。
規約：通常の圏構造と豊穣構造の合成を整合させる。
使われ方：Kerodon Construction 3.1.6.1（Tag 00TZ）、Kan の単体的圏。 -/
@[kerodon 00TZ]
instance kanObject_simplicialCategory : SimplicialCategory KanObject.{u} where
  homEquiv {X Y} := curryHomEquiv' (X := X.obj) (Y := Y.obj)
  homEquiv_id X := curry'_id X.obj
  homEquiv_comp {X Y Z} f g := curry'_comp (C := SSet.{u}) f g

/-- 概要：Kan 複体の圏の豊穣 Hom は Kan 複体。
方針：単射との pushout-product による内部 Hom の既存の Kan 性を使う。
規約：始域の Kan 性は不要だが KanObject の場合に適用する。
使われ方：Kerodon Corollary 3.1.3.4（Tag 00TN）、Construction 3.1.6.1（Tag 00TZ） の局所 Kan 性。 -/
instance kanObject_sHom_kanComplex (X Y : KanObject.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) :=
  inferInstanceAs (KanComplex ((ihom X.obj).obj Y.obj))

/-- 概要：空間の ∞ 圏 𝒮。
方針：Kan 複体の単体的圏の coherent nerve を取る。
規約：極限・余極限の主張はこの定義に含めない。
使われ方：Kerodon Construction 3.1.6.1（Tag 00TZ）、left fibration の straightening の値域。 -/
@[kerodon 00TZ, kerodon 01ZW]
def SpaceInfinity : SSet.{u + 1} := SimplicialNerve KanObject.{u}

/-- 概要：空間の ∞ 圏 𝒮 は quasicategory。
方針：内部 Hom の Kan 性と既存の γ1 を組み合わせる。
規約：追加の充填仮定を課さない。
使われ方：Kerodon Construction 3.1.6.1（Tag 00TZ）、𝒮 値の関手 ∞ 圏。 -/
@[kerodon 01YY]
instance spaceInfinity_quasicategory : Quasicategory SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory KanObject.{u}

/-- 概要：空間の ∞ 圏を値に取る関手 ∞ 圏。
方針：内部 Hom を使う。
規約：定義域 C は宇宙 u+1 に配置する。
使われ方：Kerodon §5.6（Tag 027M）、left fibration の straightening の関手側。 -/
def SpaceInfinityFunctor (C : SSet.{u + 1}) : SSet.{u + 1} := (ihom C).obj SpaceInfinity.{u}

/-- 概要：𝒮 値の関手単体集合は quasicategory。
方針：内部 Hom の quasicategory 性を使う。
規約：定義域 C は任意の単体集合。
使われ方：Kerodon §5.6（Tag 027M）、left fibration の straightening の値域の圏。 -/
instance spaceInfinityFunctor_quasicategory (C : SSet.{u + 1}) :
    Quasicategory (SpaceInfinityFunctor C) := inferInstanceAs (Quasicategory ((ihom C).obj SpaceInfinity))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
