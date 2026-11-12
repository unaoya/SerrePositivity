module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VariableSourcePrismBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftEquivalence

/-!
概要：pointed-space の始点写像と底の区間を同時に動かす全 lift prism の空間。
方針：始点写像の関手空間と区間写像空間の直積から普遍初期値データを作る。
規約：この段階では始点写像を同値に制限しない。
使われ方：Kerodon Lemma 5.6.9.1（Tag 02SN） の中間空間の周囲の構成。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：始点写像と底の区間の同時パラメーター空間。
方針：始点 fiber への関手空間と二端点固定の区間写像空間の直積を取る。
規約：係数 K は任意の単体集合。
使われ方：始点同値の空間への制限の前の周囲の空間。 -/
def pointedPrismParameterSpace (K : SSet.{u + 1}) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    SSet.{u + 1} :=
  (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace s t

/-- 概要：全ての始点写像を同時に評価する初期値の族。
方針：区間パラメーターを忘れて始点 fiber への普遍関手を評価し、全空間へ含める。
規約：初期値は始点写像の高次パラメーターに依存する。
使われ方：動く初期値の相対 lift データ。 -/
def pointedPrismInitial (K : SSet.{u + 1}) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    K ⊗ pointedPrismParameterSpace K s t ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} :=
  (K ◁ fst _ _) ≫ uncurry (𝟙 ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s))) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s

/-- 概要：始点写像と区間に依存する prism の底の族。
方針：係数と始点写像を忘れ、二端点固定の普遍区間を評価する。
規約：全ての始点写像に対して同じ区間パラメーターを使う。
使われ方：動く初期値の lift の底の図式。 -/
def pointedPrismBase (K : SSet.{u + 1}) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    Δ[1] ⊗ (K ⊗ pointedPrismParameterSpace K s t) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (Δ[1] ◁ (snd K _ ≫ snd _ _)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace s t))

/-- 概要：初期値の底は普遍区間の始点に一致する。
方針：初期値の fiber 条件と区間の始点公式を使う。
規約：始点写像を固定しない。
使われ方：相対内部 Hom へのデータを作る可換性。 -/
lemma pointedPrismInitial_base (K : SSet.{u + 1}) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    pointedPrismInitial K s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ pointedPrismBase K s t := by
  dsimp only [pointedPrismInitial, pointedPrismBase]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_zero, SSet.comp_const]

/-- 概要：底の族の終点は指定した空間 t に定値。
方針：普遍区間の終点公式を係数と始点写像の射影で引き戻す。
規約：全パラメーターでの厳密な等式。
使われ方：終点評価を t 上の fiber 値にする。 -/
lemma pointedPrismBase_one (K : SSet.{u + 1}) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ pointedPrismBase K s t = SSet.const t := by
  dsimp only [pointedPrismBase]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_one, SSet.comp_const]

/-- 概要：全ての始点写像と底の区間の相対 lift データ。
方針：動く初期値と普遍区間を初期値データへ束ねる。
規約：実際の lift の選択は行わない。
使われ方：pointed-space の同時 lift 空間の定義。 -/
def pointedPrismData (K : SSet.{u + 1}) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    pointedPrismParameterSpace K s t ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection K).pt :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (pointedPrismInitial K s t) (pointedPrismBase K s t)
    (pointedPrismInitial_base K s t)

/-- 概要：始点写像と底の区間を同時に動かした全 pointed-space lift prism の空間。
方針：動く初期値の相対内部 Hom の引き戻しを取る。
規約：始点写像を同値に制限する前の空間。
使われ方：境界制限のための中間空間の周囲の構成。 -/
def pointedPrismLiftSpace (K : SSet.{u + 1}) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection K (pointedPrismData K s t)

/-- 概要：全 pointed-space lift から始点写像と底の区間を取り出す。
方針：引き戻しのパラメーター射影を取る。
規約：両方のパラメーターを保持する。
使われ方：固定始点への制限と可縮な lift の選択。 -/
def pointedPrismLiftParameters (K : SSet.{u + 1}) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    pointedPrismLiftSpace K s t ⟶ pointedPrismParameterSpace K s t :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection K (pointedPrismData K s t)

/-- 概要：全 pointed-space lift の始点写像の射。
方針：パラメーターの第一射影を取る。
規約：底の区間パラメーターは忘れる。
使われ方：始点同値の空間への射と fiber の同定。 -/
def pointedPrismLiftSource (K : SSet.{u + 1}) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    pointedPrismLiftSpace K s t ⟶ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s) :=
  pointedPrismLiftParameters K s t ≫ fst _ _

/-- 概要：全 pointed-space lift の終点評価。
方針：動く初期値の普遍終点評価を使う。
規約：全ての高次 lift を含む空間全体の射。
使われ方：始点も動く終点制限の定義。 -/
def pointedPrismLiftEndpoint (K : SSet.{u + 1}) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    pointedPrismLiftSpace K s t ⟶ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection t) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceEndpoint _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (pointedPrismInitial K s t)
    (pointedPrismBase K s t) (pointedPrismInitial_base K s t) t (pointedPrismBase_one K s t)

/-- 概要：始点と終点を同時に制限する射。
方針：始点写像と終点写像を直積へ束ねる。
規約：始点を同値に制限した部分への適用は後で行う。
使われ方：Kerodon Lemma 5.6.9.1（Tag 02SN） の同時終点制限。 -/
def pointedPrismLiftEndpoints (K : SSet.{u + 1}) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    pointedPrismLiftSpace K s t ⟶
      (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s) ⊗
        (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection t) :=
  lift (pointedPrismLiftSource K s t) (pointedPrismLiftEndpoint K s t)

/-- 概要：全 lift から始点写像と区間への射影は trivial Kan fibration。
方針：初期値が動く相対内部 Hom の一般の底変換を適用する。
規約：全ての始点写像を同時に許す。
使われ方：中間空間の始点と底による比較。 -/
instance pointedPrismLiftParameters_trivialKanFibration
    (K : SSet.{u + 1}) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pointedPrismLiftParameters K s t) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection_trivialKanFibration _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
