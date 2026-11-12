module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitComma
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal

/-!
概要：各始域の fiber の始対象からなる普遍矢印の全部分単体集合。
方針：comma の頂点を、その始域上の fiber の始対象性で選ぶ。
規約：各点の写像空間条件からこの始対象性を導く部分は別工程。
使われ方：Kerodon §6.2.6（Tag 02FQ） の局所存在判定で普遍矢印を関手の族として選ぶ準備。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：comma の任意の頂点を自身の始域の fiber の頂点として表示する。
方針：零次の定値単体の等式を使う。
規約：始域の頂点は unitCommaSource の像。
使われ方：普遍矢印の頂点条件。 -/
noncomputable def unitCommaVertexInFiber {X Y : SSet.{u}} (G : Y ⟶ X)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G).app (Opposite.op ⦋0⦌) v)) _⦋0⦌ :=
  ⟨v, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _).symm⟩

/-- 概要：comma の頂点がその始域の上で普遍矢印となる条件。
方針：固定始域の fiber 内の始対象性を要求する。
規約：fiber の対象は y と矢印 x→G(y) の両方を保持する。
使われ方：普遍矢印の全部分単体集合を定める。 -/
def IsUniversalUnitCommaVertex {X Y : SSet.{u}} (G : Y ⟶ X)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (unitCommaVertexInFiber G v)

/-- 概要：普遍矢印の頂点が張る全部分単体集合。
方針：comma の頂点を始域上の始対象条件で制限する。
規約：高次単体は全ての頂点が条件を満たすもの。
使われ方：単位を普遍矢印の coherent な族へ制限する。 -/
noncomputable def universalUnitComma {X Y : SSet.{u}} (G : Y ⟶ X) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) (IsUniversalUnitCommaVertex G) : SSet.{u})

/-- 概要：普遍矢印の全部分単体集合から comma への包含。
方針：頂点条件で定義した全部分複体の包含。
規約：全ての単体で単射。
使われ方：始域・標的の射影の制限。 -/
noncomputable def universalUnitCommaι {X Y : SSet.{u}} (G : Y ⟶ X) :
    universalUnitComma G ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) (IsUniversalUnitCommaVertex G)).ι

/-- 概要：普遍矢印の包含は inner fibration。
方針：頂点条件で定めた全部分複体の一般の包含の定理を使う。
規約：G の始域・標的の quasicategory 性は不要。
使われ方：始域射影の充填性の合成。 -/
instance universalUnitCommaι_innerFibration {X Y : SSet.{u}} (G : Y ⟶ X) :
    InnerFibration (universalUnitCommaι G) := by
  change InnerFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) (IsUniversalUnitCommaVertex G)).ι
  infer_instance

/-- 概要：普遍矢印の始域への射影。
方針：包含の後に comma の始域射影を続ける。
規約：この射の同値性は定義では仮定しない。
使われ方：局所存在判定で必要な全体の射。 -/
noncomputable def universalUnitCommaProjection {X Y : SSet.{u}} (G : Y ⟶ X) :
    universalUnitComma G ⟶ X :=
  universalUnitCommaι G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G

/-- 概要：普遍矢印の始域射影は inner fibration。
方針：全部分複体の包含と comma の始域射影の inner fibration 性を合成する。
規約：ここでは外側ホーンの充填や同値性は主張しない。
使われ方：局所存在で残る持ち上げ条件を分離する。 -/
instance universalUnitCommaProjection_innerFibration {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X) :
    InnerFibration (universalUnitCommaProjection G) :=
  ⟨innerFibrations.comp_mem _ _ (InnerFibration.mem (q := universalUnitCommaι G))
    (InnerFibration.mem (q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G))⟩

/-- 概要：普遍矢印の全部分単体集合は quasicategory。
方針：始域への inner fibration と X の quasicategory 性を使う。
規約：G の始域・標的は quasicategory。
使われ方：普遍矢印の図式の圏構造。 -/
instance universalUnitComma_quasicategory {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (G : Y ⟶ X) : Quasicategory (universalUnitComma G) :=
  quasicategory_of_innerFibration (universalUnitCommaProjection G)

/-- 概要：指定単位の各成分が comma 内の普遍矢印である条件。
方針：単位の切断の全頂点が始域の fiber の始対象であることを要求する。
規約：各点の写像空間条件との同値はまだ主張しない。
使われ方：単位の切断を普遍矢印へ制限する中間仮定。 -/
def UnitCommaInitialCondition {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) : Prop :=
  ∀ x : X _⦋0⦌,
    IsUniversalUnitCommaVertex G ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection η).app (Opposite.op ⦋0⦌) x)

/-- 概要：fiber の底の頂点を等式で移しても同じ頂点の始対象性は変わらない。
方針：底の等式を消去し、部分型の外延性を使う。
規約：充填性の仮定は不要。
使われ方：単位の切断の fiber の添字を指定した x に揃える。 -/
lemma isInitialVertex_vertexFiber_congr {E B : SSet.{u}} (p : E ⟶ B)
    {b b' : B _⦋0⦌} (h : b = b') (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌)
    (v' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b') _⦋0⦌) (hv : v.val = v'.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v' := by
  subst b'
  have he : v = v' := Subtype.ext hv
  subst v'
  rfl

/-- 概要：単位の普遍矢印条件は各 x 上の指定頂点の始対象性と同値。
方針：単位の切断の始域が厳密に x である等式で fiber の添字を揃える。
規約：二つの条件は同じ選んだ単位代表を使う。
使われ方：各点の写像空間条件と固定始域の fiber の始対象性を照合する。 -/
lemma unitCommaInitialCondition_iff {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) :
    UnitCommaInitialCondition η ↔ ∀ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex η x) := by
  have hv (x : X _⦋0⦌) :
      IsUniversalUnitCommaVertex G ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection η).app (Opposite.op ⦋0⦌) x) ↔
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex η x) := by
    have hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection η).app (Opposite.op ⦋0⦌) x) = x :=
      ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection_source η) (Opposite.op ⦋0⦌)) x
    exact isInitialVertex_vertexFiber_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) hx
      (unitCommaVertexInFiber G ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection η).app (Opposite.op ⦋0⦌) x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex η x) rfl
  exact ⟨fun h x ↦ (hv x).mp (h x), fun h x ↦ (hv x).mpr (h x)⟩

/-- 概要：始対象条件を満たす単位は普遍矢印の単体集合への切断を与える。
方針：頂点条件によって元の単位の切断を全部分複体へ持ち上げる。
規約：指定された η の代表に由来する同じ切断を用いる。
使われ方：局所存在での関手の coherent な族。 -/
noncomputable def universalUnitCommaSection {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (hη : UnitCommaInitialCondition η) : X ⟶ universalUnitComma G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (IsUniversalUnitCommaVertex G) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection η) hη

/-- 概要：制限した単位の切断の包含は元の切断。
方針：全部分複体への持ち上げの公式。
規約：厳密な射の等式。
使われ方：指定単位の情報を保つ。 -/
lemma universalUnitCommaSection_ι {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (hη : UnitCommaInitialCondition η) :
    universalUnitCommaSection η hη ≫ universalUnitCommaι G = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection η :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 概要：普遍矢印へ制限した単位は始域射影の厳密な切断。
方針：包含後の公式と元の単位の切断条件を使う。
規約：始域 X は同じ。
使われ方：射影の頂点上の全射性を供給する。 -/
lemma universalUnitCommaSection_projection {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (hη : UnitCommaInitialCondition η) :
    universalUnitCommaSection η hη ≫ universalUnitCommaProjection G = 𝟙 X := by
  rw [universalUnitCommaProjection, ← Category.assoc, universalUnitCommaSection_ι,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection_source]

/-- 概要：普遍矢印へ制限しても単位の標的関手は F。
方針：包含後の切断の一致と元の標的公式を使う。
規約：指定された関手 F を保つ。
使われ方：局所存在から元の随伴対へ戻す。 -/
lemma universalUnitCommaSection_target {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (hη : UnitCommaInitialCondition η) :
    universalUnitCommaSection η hη ≫ (universalUnitCommaι G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G) = F := by
  rw [← Category.assoc, universalUnitCommaSection_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection_target]

/-- 概要：単位の始対象条件の下で普遍矢印の始域射影は頂点上全射。
方針：厳密な切断を頂点に適用する。
規約：同値性や充満忠実性はこの補題では要求・主張しない。
使われ方：trivial Kan fibration の判定の零次の条件。 -/
lemma universalUnitCommaProjection_surjective {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (hη : UnitCommaInitialCondition η) :
    Function.Surjective ((universalUnitCommaProjection G).app (Opposite.op ⦋0⦌)) := by
  intro x
  exact ⟨(universalUnitCommaSection η hη).app (Opposite.op ⦋0⦌) x,
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (universalUnitCommaSection_projection η hη) (Opposite.op ⦋0⦌)) x⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
