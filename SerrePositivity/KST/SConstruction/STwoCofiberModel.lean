module
public import SerrePositivity.KST.SConstruction.STwoCofiberLifting
public import SerrePositivity.KST.SConstruction.CofiberFamilies
public import SerrePositivity.KST.SConstruction.FunctorStability
public import SerrePositivity.KST.SConstruction.TrivialFibrationStability
public import SerrePositivity.KST.SConstruction.StableModels
public import SerrePositivity.KST.SConstruction.MultiSTrivialFibration

/-! # S₂ と cofiber 正方形の安定な模型の比較
概要：cofiber 正方形全体を安定な模型とし、S₂ の制限とその切断の完全性を証明する。
方針：二つの trivial Kan fibration で普遍性を移し、切断の完全性は制限によって反映する。
規約：零対象を一つに固定した部分模型には置換しない。使われ方：McCarthy の正方形の図式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：cofiber 正方形全体は quasicategory。
方針：正方形の内部 Hom の全部分複体。
規約：C の安定性は不要。使われ方：制限による普遍性の輸送。 -/
instance cofiberDiagrams_quasicategory (C : SSet.{u}) [Quasicategory C] :
    Quasicategory (cofiberDiagrams C) :=
  inferInstanceAs (Quasicategory
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C) IsCofiberDiagramVertex :
      SSet.{u}))

/-- 概要：安定な C の cofiber 正方形全体は安定。
方針：入力の辺への trivial Kan fibration で関手圏の安定性を反映する。
規約：既存の安定性の定義を使う。使われ方：反復 S を適用する入力。 -/
instance cofiberDiagrams_isStable (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (cofiberDiagrams C) := isStable_of_trivialKanFibration (cofiberProjection C)

/-- 概要：S₂ の正方形への制限は零対象と全押し出しを保つ。
方針：trivial Kan fibration の普遍性の保存。
規約：C の安定性は不要。使われ方：正方形表示との完全な比較。 -/
lemma sTwoCofiberRestriction_preservesSConstructionData (C : SSet.{u}) [Quasicategory C] :
    PreservesSConstructionData (sTwoCofiberRestriction C) :=
  preservesSConstructionData_of_trivialKanFibration _

/-- 概要：cofiber 正方形全体を安定な入力としてまとめる。
方針：quasicategory 性と安定性を添える。
規約：全ての零角の選択を保持する。使われ方：加法性の正方形表示。 -/
def cofiberStableModel (X : StableModel.{u}) : StableModel.{u} :=
  { carrier := cofiberDiagrams X.carrier
    quasicategory := inferInstance
    stable := inferInstance }

/-- 概要：S₂ の制限を完全関手の射としてまとめる。
方針：全押し出しの保存から cofiber 保存を取り出す。
規約：底の射は元の制限そのもの。使われ方：反復 S• による比較。 -/
def sTwoCofiberComparison (X : StableModel.{u}) : sStableModel 2 X ⟶ cofiberStableModel X :=
  ⟨sTwoCofiberRestriction X.carrier,
    (sTwoCofiberRestriction_preservesSConstructionData X.carrier).toCofiberData⟩

/-- 概要：任意の cofiber 正方形の族に外側の零対角を単体的に補う切断。
方針：中央正方形への制限の trivial Kan fibration の切断から選ぶ。
規約：対象ごとの選択には弱めない。使われ方：S₂ 図式への補完。 -/
def sTwoCofiberSection (C : SSet.{u}) [Quasicategory C] : cofiberDiagrams C ⟶ sConstruction 2 C :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (sTwoCofiberRestriction C))

/-- 概要：切断による補完は指定した cofiber 正方形を厳密に回収する。
方針：切断の仕様。
規約：全単体での等号。使われ方：正方形の図式を保つ補完。 -/
lemma sTwoCofiberSection_projection (C : SSet.{u}) [Quasicategory C] :
    sTwoCofiberSection C ≫ sTwoCofiberRestriction C = 𝟙 _ :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (sTwoCofiberRestriction C))

/-- 概要：切断による補完も零対象と全押し出しを保つ。
方針：制限による普遍性の反映と、切断の厳密な右逆の式を使う。
規約：C の安定性は不要。使われ方：完全関手としての逆向きの比較。 -/
lemma sTwoCofiberSection_preservesSConstructionData (C : SSet.{u}) [Quasicategory C] :
    PreservesSConstructionData (sTwoCofiberSection C) := by
  constructor
  · intro z hz
    apply (isZeroVertex_iff_of_trivialKanFibration (sTwoCofiberRestriction C) _).2
    have he := ConcreteCategory.congr_hom
      (NatTrans.congr_app (sTwoCofiberSection_projection C) (Opposite.op ⦋0⦌)) z
    change (sTwoCofiberRestriction C).app (Opposite.op ⦋0⦌)
      ((sTwoCofiberSection C).app (Opposite.op ⦋0⦌) z) = z at he
    rw [he]
    exact hz
  · intro F hF
    apply (isPushoutSquare_iff_postcomp_of_trivialKanFibration (sTwoCofiberRestriction C) _).2
    rw [Category.assoc, sTwoCofiberSection_projection, Category.comp_id]
    exact hF

/-- 概要：切断による補完を安定な入力間の完全関手としてまとめる。
方針：零対象と全押し出しの保存から cofiber 保存を取り出す。
規約：比較の切断を自然な選択とは主張しない。使われ方：反復 S• の逆向きの比較。 -/
def sTwoCofiberInverse (X : StableModel.{u}) : cofiberStableModel X ⟶ sStableModel 2 X :=
  ⟨sTwoCofiberSection X.carrier,
    (sTwoCofiberSection_preservesSConstructionData X.carrier).toCofiberData⟩

/-- 概要：制限して補完し直した図式は元の S₂ 図式と関手として同型。
方針：同じ中央正方形上の二つの持ち上げを比較する。
規約：cofiber 正方形は保持するが S₂ の厳密な逆射とは主張しない。
使われ方：正方形表示との ∞ 圏の同値。 -/
def sTwoCofiberSection_comparison (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (sTwoCofiberRestriction C ≫ sTwoCofiberSection C) (𝟙 (sConstruction 2 C)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration (sTwoCofiberRestriction C) _ _ (by
    rw [Category.assoc, sTwoCofiberSection_projection, Category.comp_id, Category.id_comp])

/-- 概要：S₂ と全 cofiber 正方形の quasicategory は同値。
方針：元の制限写像の trivial Kan fibration から同値を構成する。
規約：固定零対象の模型への同値は含めない。使われ方：正方形表示への ∞ 圏の比較。 -/
def sTwoCofiberEquivalence (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (sConstruction 2 C) (cofiberDiagrams C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (sTwoCofiberRestriction C)

/-- 概要：任意回数の core S 実現でも正方形表示への比較は弱同値。
方針：比較の底の trivial Kan fibration に、反復 S・core・対角実現の保存を適用する。
規約：引用や追加の同値仮定は不要。使われ方：正方形表示で証明する加法性を既存の段へ移す。 -/
lemma sTwoCofiberComparison_realization_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor r).map (sTwoCofiberComparison X))) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (sTwoCofiberComparison X).val :=
    sTwoCofiberRestriction_trivialKanFibration X.carrier
  exact multiRealizationFunctor_map_localized_isIso r (sTwoCofiberComparison X)

end SerrePositivity.KST.SConstruction
