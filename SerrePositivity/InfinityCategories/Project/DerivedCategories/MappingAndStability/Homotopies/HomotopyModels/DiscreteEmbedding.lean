module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.FreeResolution
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.NerveInclusion
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.InfinityCategory
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # 離散可換代数の導来 ∞ 圏への埋め込み

概要：S 上の可換環を忘却し、関手的 semifree 解像度を取って dg nerve の頂点と辺へ送る。
方針：自由解像度を閉零圏へ持ち上げ、通常の nerve と標準包含を合成する。
規約：CRing_{S/} は Under (CommRingCat.of S)。使われ方：D(R) レベルの BS 界面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
open scoped _root_.Simplicial
variable (S : Type u) [CommRing S]

/-- 概要：semifree の閉零圏から通常の複体への充満忠実関手。
方針：充満 dg 包含の閉零関手と複体との比較を合成する。
規約：対象の複体をそのまま取り出す。使われ方：解像度関手の射の持ち上げ。 -/
abbrev semifreeClosedToComplex : ClosedCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) ⥤ Complex S :=
  (dgFullSubcategoryInclusion S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S)).onClosed ⋙ closedToComplex S

/-- 概要：閉零圏からの複体比較は充満である。
方針：充満 dg 包含と既存比較の充満性を合成する。
規約：像の対象間の全鎖写像を持ち上げる。使われ方：関手的解像度。 -/
instance semifreeClosedToComplex_full : (semifreeClosedToComplex S).Full := by
  unfold semifreeClosedToComplex
  infer_instance

/-- 概要：閉零圏からの複体比較は忠実である。
方針：充満 dg 包含と既存比較の忠実性を合成する。
規約：鎖写像の等式を反映する。使われ方：持ち上げた関手の法則。 -/
instance semifreeClosedToComplex_faithful : (semifreeClosedToComplex S).Faithful := by
  unfold semifreeClosedToComplex
  infer_instance

/-- 概要：加群を関手的 semifree 解像度へ送る通常の関手。
方針：自由余鎖解像度の対象に semifree 性を添え、射を充満忠実比較で持ち上げる。
規約：Semifree の射は閉次数零の射。使われ方：離散代数の nerve の写像。 -/
def moduleSemifreeResolutionFunctor : ModuleCat.{u} S ⥤ ClosedCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) where
  obj M := ForgetEnrichment.of (Complex S)
    (⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution S).obj M, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution_semifree S M⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)
  map f := (semifreeClosedToComplex S).preimage ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution S).map f)
  map_id M := by
    apply (semifreeClosedToComplex S).map_injective
    rw [Functor.map_preimage, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution S).map_id,
      (semifreeClosedToComplex S).map_id]
    rfl
  map_comp f g := by
    apply (semifreeClosedToComplex S).map_injective
    simp only [Functor.map_preimage, Functor.map_comp]

/-- 概要：閉零圏へ持ち上げた解像度を複体として読むと元の自由解像度になる。
方針：対象では恒等、射では充満関手の逆像の公式を使う。
規約：自然同型で比較する。使われ方：自然な増大射と擬同型の保持。 -/
def moduleSemifreeResolutionComparison :
    moduleSemifreeResolutionFunctor S ⋙ semifreeClosedToComplex S ≅ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution S :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    change (semifreeClosedToComplex S).map
      ((moduleSemifreeResolutionFunctor S).map f) ≫ 𝟙 _ =
        𝟙 _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution S).map f
    dsimp only [moduleSemifreeResolutionFunctor]
    rw [Functor.map_preimage, Category.comp_id, Category.id_comp])

/-- 概要：semifree 解像度を元の加群の次数零複体へ送る自然な増大射。
方針：自由解像度との比較自然同型と既知の自然な増大射を合成する。
規約：通常の複体として評価した自然変換。使われ方：関手的解像度の比較。 -/
def moduleSemifreeResolutionAugmentation :
    moduleSemifreeResolutionFunctor S ⋙ semifreeClosedToComplex S ⟶
      HomologicalComplex.single (ModuleCat S) (.up ℤ) 0 :=
  (moduleSemifreeResolutionComparison S).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentationNat S

/-- 概要：semifree 解像度の自然な増大射は各加群で擬同型である。
方針：自由解像度の増大擬同型に比較の同型を合成する。
規約：全整数次数のホモロジーでの同型。使われ方：D(S) での離散加群の代表。 -/
theorem moduleSemifreeResolutionAugmentation_quasiIso (M : ModuleCat.{u} S) :
    QuasiIso ((moduleSemifreeResolutionAugmentation S).app M) := by
  haveI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentation_quasiIso S M
  change QuasiIso
    ((moduleSemifreeResolutionComparison S).hom.app M ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentation S M)
  infer_instance

/-- 概要：S の下の可換環を S 加群へ忘却する。
方針：S 代数との標準同値を通し、代数の加群忘却関手を合成する。
規約：対象の S 作用は構造準同型によるもの。使われ方：D(S) への離散埋め込み。 -/
def discreteAlgebraModule : Under (CommRingCat.of S) ⥤ ModuleCat.{u} S :=
  (commAlgCatEquivUnder (CommRingCat.of S)).inverse ⋙
    forget₂ (CommAlgCat.{u} S) (AlgCat.{u} S) ⋙ forget₂ (AlgCat.{u} S) (ModuleCat.{u} S)

/-- 概要：離散 S 代数の通常の nerve を導来 ∞ 圏へ送る。
方針：S 加群への忘却と関手的 semifree 解像度の nerve を標準 dg nerve 包含に合成する。
規約：CRing_{S/} の対象・射を関手的に送る。使われ方：D(R) レベルの界面の離散入力。 -/
def discreteEmbedding : nerve (Under (CommRingCat.of S)) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S :=
  nerveMap (discreteAlgebraModule S ⋙ moduleSemifreeResolutionFunctor S) ≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)

/-- 概要：離散代数の像の零次ホモロジーは元の S 加群に同型である。
方針：頂点の定義を評価し、関手的自由解像度の増大擬同型を使う。
規約：代数構造を主張せず S 加群として比較する。使われ方：離散埋め込みの H⁰ 同定。 -/
def discreteEmbeddingHomologyZeroIso (B : Under (CommRingCat.of S)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)
      ((discreteEmbedding S).app _ (ComposableArrows.mk₀ B))).val).homology 0 ≅
        (discreteAlgebraModule S).obj B :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainHomologyZeroIso S ((discreteAlgebraModule S).obj B)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
