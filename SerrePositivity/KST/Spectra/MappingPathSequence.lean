module
public import SerrePositivity.KST.Spectra.PullbackKanSequence

public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.MappingPathSpace
public import SerrePositivity.KST.Spectra.MappingKanSequence
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence

/-!
概要：任意の Kan 列の射の厳密な mapping path 因子分解。
方針：始点評価の列を射に沿って引き戻し、終点評価と定数 path を使う。
規約：中間列の構造射の単射性は次の cofibrant 置換で確保する。
使われ方：BF 1978 §2、Goerss–Jardine I §7、HTT A.3.3。任意の射の fiber 列。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.KanSequence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：path 列の端点評価は各段で Kan fibration。
方針：自由な path の端点評価の fibration 性を使う。
規約：面添字零と一の両方に適用する。
使われ方：BF 1978 §2、Goerss–Jardine I §7。mapping path 列の引き戻し。 -/
instance freePathEvaluation_fibration (Y : KanSequence.{u}) (i : Fin 2) :
    ∀ n, Fibration ((Y.freePathEvaluation i).app n).right := fun n ↦
  inferInstanceAs (Fibration (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint (Y.level n).space i).right)

/-- 概要：任意の Kan 列の射の mapping path 列。
方針：始点評価の列を元の射に沿って段ごとに引き戻す。
規約：各段の Kan 性は始点評価の fibration 性から従う。
使われ方：BF 1978 §2、Goerss–Jardine I §7。置換前の中間列。 -/
def mappingPathSequence {X Y : KanSequence.{u}} (f : Hom X Y) : KanSequence.{u} :=
  pullbackSequence (Y.freePathEvaluation 1) f

/-- 概要：mapping path 列から元の源への厳密な射影。
方針：引き戻し列の第二射影を使う。
規約：各段は既存の mapping path の源射影。
使われ方：BF 1978 §2。中間列の Ω 条件の移送。 -/
def mappingPathSource {X Y : KanSequence.{u}} (f : Hom X Y) : Hom (mappingPathSequence f) X :=
  pullbackSecond (Y.freePathEvaluation 1) f

/-- 概要：mapping path 列から元の標的への厳密な終点射。
方針：第一射影と終点評価の列の射を合成する。
規約：各段は Kan fibration となる。
使われ方：BF 1978 §2、Goerss–Jardine I §7。任意の射の fiber の置換。 -/
def mappingPathTarget {X Y : KanSequence.{u}} (f : Hom X Y) : Hom (mappingPathSequence f) Y :=
  (pullbackFirst (Y.freePathEvaluation 1) f).comp (Y.freePathEvaluation 0)

/-- 概要：元の Kan 列から mapping path 列への定数 path の厳密な比較射。
方針：定数 path の列の射と恒等射を引き戻し列へ貼る。
規約：構造射との可換性も厳密に保持する。
使われ方：BF 1978 §2、Goerss–Jardine I §7。元の射の因子分解。 -/
def mappingPathComparison {X Y : KanSequence.{u}} (f : Hom X Y) :
    Hom X (mappingPathSequence f) :=
  pullbackLift (Y.freePathEvaluation 1) f (f.comp Y.freePathConstant)
    { app n := 𝟙 _, comm n := by simp } (fun n ↦ by
      change (f.app n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath (Y.level n).space) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint (Y.level n).space 1 = (𝟙 _) ≫ f.app n
      simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath_endpoint, Category.comp_id, Category.id_comp])

/-- 概要：mapping path の源射影は各段で全ての単射に RLP を持つ。
方針：始点評価の RLP を引き戻す。
規約：構造射の単射性を要求しない。
使われ方：BF 1978 §2、HTT A.3.3。中間列の Ω 条件。 -/
theorem mappingPathSource_rlp {X Y : KanSequence.{u}} (f : Hom X Y) (n : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((mappingPathSource f).app n).right :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction_rlp (f.app n)

/-- 概要：mapping path の終点射は各段で Kan fibration。
方針：点つき単体集合の mapping path の相対ホーン充填を使う。
規約：Kan 列の任意の射に適用する。
使われ方：BF 1978 §2、Goerss–Jardine I §7。段ごとの fibration 置換。 -/
instance mappingPathTarget_fibration {X Y : KanSequence.{u}} (f : Hom X Y) :
    ∀ n, Fibration ((mappingPathTarget f).app n).right := fun n ↦
  inferInstanceAs (Fibration (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection (f.app n)).right)

/-- 概要：mapping path の比較射と源射影の合成は各段で恒等射。
方針：定数 path の引き戻しの第二射影を計算する。
規約：厳密な射の等式。
使われ方：BF 1978 §2。比較射の π_* 同型。 -/
@[reassoc (attr := simp)]
theorem mappingPathComparison_source {X Y : KanSequence.{u}} (f : Hom X Y) (n : ℕ) :
    (mappingPathComparison f).app n ≫ (mappingPathSource f).app n = 𝟙 _ :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_retraction (f.app n)

/-- 概要：mapping path の比較射と終点射の合成は各段で元の射。
方針：定数 path の終点評価を計算する。
規約：ホモトピーによる等式ではない。
使われ方：BF 1978 §2。元の射の厳密な因子分解。 -/
@[reassoc (attr := simp)]
theorem mappingPathComparison_target {X Y : KanSequence.{u}} (f : Hom X Y) (n : ℕ) :
    (mappingPathComparison f).app n ≫ (mappingPathTarget f).app n = f.app n :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_projection (f.app n)

/-- 概要：mapping path 列の比較射は各段で全基点の π_* 同型。
方針：源射影の RLP による π_* 同型を、恒等射となる合成から打ち消す。
規約：零次数も含む。
使われ方：BF 1978 §2、Goerss–Jardine I §7。fibration 置換の同値。 -/
theorem mappingPathComparison_piIsomorphism {X Y : KanSequence.{u}}
    (f : Hom X Y) (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((mappingPathComparison f).app n).right := by
  have hr : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((mappingPathSource f).app n).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (mappingPathSource_rlp f n)
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := ((mappingPathSource f).app n).right) _ hr
  have h : ((mappingPathComparison f).app n).right ≫ ((mappingPathSource f).app n).right =
      𝟙 (X.level n).space.right := congrArg Under.Hom.right (mappingPathComparison_source f n)
  rw [h]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _

/-- 概要：源が Ω 条件を満たすなら mapping path 列も Ω 条件を満たす。
方針：源射影の各段の全単射への RLP により Ω 条件を移す。
規約：標的の Ω 条件はこの証明には不要。
使われ方：BF 1978 §2、HA §1.4.2、HTT A.3.3。任意の Ω スペクトルの射の置換。 -/
theorem mappingPathSequence_omegaCondition {X Y : KanSequence.{u}}
    (f : Hom X Y) (hX : X.OmegaCondition) : (mappingPathSequence f).OmegaCondition :=
  (mappingPathSource f).omegaCondition_of_target (mappingPathSource_rlp f) hX

end

end SerrePositivity.KST.Spectra.KanSequence
