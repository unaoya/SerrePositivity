module
public import SerrePositivity.KST.SConstruction.FirstRowFibration
public import SerrePositivity.KST.SConstruction.CoreTrivialFibration
public import SerrePositivity.KST.SConstruction.CoreSimplicial
public import SerrePositivity.KST.SConstruction.LocalizedPiComparison
public import SerrePositivity.KST.SConstruction.LocalizedTrivialFibrations
public import SerrePositivity.KST.SConstruction.CofiberMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint
public import SerrePositivity.KST.SConstruction.StableModels

/-! # S₁ と元の安定圏との自然な比較
概要：第一行の一点の nerve の関手圏を元の圏と同一視し、S₁ の比較射を作る。
方針：第一行制限の trivial Kan fibration に実際の単体集合の同型を合成する。
規約：逆射を自然に選ぶとは主張しない。使われ方：反復 S の構造射の源の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：一次の第一行の添字は終対象と同型。
方針：Δ[0] との既存の同型を合成する。
規約：ULift の宇宙を保持する。使われ方：一点からの内部 Hom の同一視。 -/
def firstRowOneUnitIso : firstRowNerve.{u} 1 ≅ 𝟙_ SSet.{u} :=
  (firstRowSimplexIso 0).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stdSimplexZeroUnitIso

/-- 概要：一次の第一行の関手圏は元の圏と自然に同型。
方針：添字の同型による前合成と単位内部 Hom の同型を使う。
規約：全単体集合に適用する。使われ方：S₁ の比較の値域の整理。 -/
def firstRowOneHomNatIso : ihom (firstRowNerve.{u} 1) ≅ 𝟭 SSet.{u} :=
  (show ihom (firstRowNerve.{u} 1) ≅ ihom (𝟙_ SSet.{u}) from {
    hom := pre firstRowOneUnitIso.inv
    inv := pre firstRowOneUnitIso.hom
    hom_inv_id := by rw [← pre_map, firstRowOneUnitIso.hom_inv_id, pre_id]
    inv_hom_id := by rw [← pre_map, firstRowOneUnitIso.inv_hom_id, pre_id] }) ≪≫
      (MonoidalClosed.unitNatIso (C := SSet.{u})).symm

/-- 概要：S₁ の第一行を元の圏へ評価する比較射。
方針：第一行制限と一点関手圏の同型を合成する。
規約：零対象や補完の選択を含まない。使われ方：反復 S の一次段の比較。 -/
def sOneComparison (C : SSet.{u}) : sConstruction 1 C ⟶ C :=
  firstRowRestriction 1 C ≫ firstRowOneHomNatIso.hom.app C

/-- 概要：安定な quasicategory の S₁ 比較は trivial Kan fibration。
方針：第一行制限に同型を合成する。
規約：頂点の全射性を追加仮定しない。使われ方：自然な逆射の代わりの比較。 -/
instance sOneComparison_trivialKanFibration (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (sOneComparison C) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (firstRowOneHomNatIso.hom.app C) := inferInstance
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem⟩

/-- 概要：第一行制限は cofiber を保つ後合成と可換。
方針：gapped 包含の後合成の式と内部 Hom の自然性を使う。
規約：終域は quasicategory。使われ方：S₁ の比較の自然性。 -/
lemma firstRowRestriction_sPostcompCofiber (n : ℕ) {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) :
    sPostcompCofiber n f hf ≫ firstRowRestriction n D =
      firstRowRestriction n C ≫ (ihom (firstRowNerve n)).map f := by
  unfold firstRowRestriction
  rw [← Category.assoc, sPostcompCofiber_ι, Category.assoc,
    (pre (firstRowInclusion n)).naturality]
  simp only [Category.assoc]

/-- 概要：S₁ の比較は cofiber を保つ入力の射について自然。
方針：第一行制限と一点の内部 Hom の自然な同型を合成する。
規約：選んだ零対象の保存は不要。使われ方：構造射の自然な比較。 -/
lemma sOneComparison_naturality {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) :
    sPostcompCofiber 1 f hf ≫ sOneComparison D = sOneComparison C ≫ f := by
  unfold sOneComparison
  rw [← Category.assoc, firstRowRestriction_sPostcompCofiber, Category.assoc,
    firstRowOneHomNatIso.hom.naturality]
  rfl

/-- 概要：一次段の core から元の圏の core への比較。
方針：S₁ の比較に core 関手を適用する。
規約：写像の定義には安定性は不要。使われ方：反復実現の構造射の源の比較。 -/
def coreSOneComparison (C : SSet.{u}) :
    coreSConstruction 1 C ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sOneComparison C)

/-- 概要：安定な入力の一次段の core の比較は trivial Kan fibration。
方針：S₁ の比較の全境界充填性を core に制限する。
規約：core を Kan にする外部仮定は追加しない。使われ方：一次段の弱同値比較。 -/
instance coreSOneComparison_trivialKanFibration (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (coreSOneComparison C) :=
  coreMap_trivialKanFibration (sOneComparison C)

/-- 概要：一次段の core の比較は全基点・全次数で π_* 同型。
方針：trivial Kan fibration の局所化可逆性を L9 の実際の π_* に移す。
規約：零次数も含む。使われ方：S₁ と元の圏の Kan 模型の同値。 -/
lemma coreSOneComparison_piIsomorphism (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (coreSOneComparison C) := by
  apply kanPiIsomorphism_of_localized_isIso
  exact map_isIso_of_trivialKanFibration AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions) (coreSOneComparison C)

/-- 概要：core の一次段の比較は cofiber を保つ後合成について自然。
方針：元の S₁ の比較の自然性を core 関手で写す。
規約：選択した零対象の保存は要求しない。使われ方：反復の比較の自然性。 -/
lemma coreSOneComparison_naturality {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sPostcompCofiber 1 f hf) ≫ coreSOneComparison D =
      coreSOneComparison C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap f := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (sPostcompCofiber 1 f hf) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (sOneComparison D) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (sOneComparison C) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map f
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map_comp,
    sOneComparison_naturality]

/-- 概要：安定な入力における core の一次段の比較の自然変換。
方針：各成分に自然な S₁ の比較を取る。
規約：逆射の自然な選択は含めない。使われ方：多単体的実現の比較図式。 -/
def coreSOneComparisonNat :
    sEndofunctor 1 ⋙ stableModelForget ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor ⟶
      stableModelForget ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor where
  app X := coreSOneComparison X.carrier
  naturality {_X _Y} f := coreSOneComparison_naturality f.val f.property

end SerrePositivity.KST.SConstruction
