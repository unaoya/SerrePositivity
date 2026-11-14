module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.TransformationFamilies
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InnerProductProjection

/-!
概要：矢印 x→G(y) の comma の単体集合と、指定単位の切断。
方針：区間の境界制限の引き戻しを使い、単位のホモトピー代表を持ち上げる。
規約：ここでは普遍矢印への制限や局所存在の結論は主張しない。
使われ方：Kerodon §6.2.6（Tag 02FQ） の局所存在判定の図式の準備。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：端点の組 (x,y) を x と G(y) の境界図式に送る射。
方針：二つの射影の境界図式を curry する。
規約：G は任意の単体集合の射。
使われ方：矢印の単体集合の引き戻しの底を指定する。 -/
def unitCommaBoundary {X Y : SSet.{u}} (G : Y ⟶ X) :
    X ⊗ Y ⟶ (ihom (boundary 1 : SSet.{u})).obj X :=
  curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (fst X Y) (snd X Y ≫ G))

/-- 概要：矢印 x→G(y) とその coherent な族の単体集合。
方針：区間からの関手を、端点の組で指定した境界上へ引き戻す。
規約：端点の組と区間からの射を保持する。
使われ方：指定単位から普遍矢印の部分単体集合へ進む中間図式。 -/
noncomputable def unitComma {X Y : SSet.{u}} (G : Y ⟶ X) : SSet.{u} :=
  pullback ((pre (boundary 1).ι).app X) (unitCommaBoundary G)

/-- 概要：comma の矢印を区間からの関手として取り出す。
方針：引き戻しの第一射影。
規約：始域・標的も境界から回収できる。
使われ方：単位の矢印の族の評価。 -/
noncomputable def unitCommaArrow {X Y : SSet.{u}} (G : Y ⟶ X) :
    unitComma G ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  pullback.fst _ _

/-- 概要：comma の端点の組への射影。
方針：引き戻しの第二射影。
規約：底は X×Y。
使われ方：普遍矢印の始域と標的を記録する。 -/
noncomputable def unitCommaPair {X Y : SSet.{u}} (G : Y ⟶ X) : unitComma G ⟶ X ⊗ Y :=
  pullback.snd _ _

/-- 概要：comma の矢印の始域への射影。
方針：端点の組の第一射影を続ける。
規約：値は X。
使われ方：単位の切断の底への射。 -/
noncomputable def unitCommaSource {X Y : SSet.{u}} (G : Y ⟶ X) : unitComma G ⟶ X :=
  unitCommaPair G ≫ fst X Y

/-- 概要：comma の矢印の標的 y への射影。
方針：端点の組の第二射影を続ける。
規約：値は X ではなく Y。
使われ方：単位の切断から指定関手 F を回収する。 -/
noncomputable def unitCommaTarget {X Y : SSet.{u}} (G : Y ⟶ X) : unitComma G ⟶ Y :=
  unitCommaPair G ≫ snd X Y

/-- 概要：comma の端点の組への射影は inner fibration。
方針：単射である区間の境界への制限の inner fibration を引き戻す。
規約：この充填性には X の quasicategory 性だけを使う。
使われ方：comma の quasicategory 性と相対的な充填。 -/
instance unitCommaPair_innerFibration {X Y : SSet.{u}} [Quasicategory X] (G : Y ⟶ X) :
    InnerFibration (unitCommaPair G) :=
  ⟨innerFibrations.pullback_snd _ _ (InnerFibration.mem (q := (pre (boundary 1).ι).app X))⟩

/-- 概要：comma の始域射影は inner fibration。
方針：端点の組への射影と直積の第一射影の合成を使う。
規約：G 自体の fibration 性は不要。
使われ方：各始域 x 上の comma の fiber を quasicategory として扱う。 -/
instance unitCommaSource_innerFibration {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X) :
    InnerFibration (unitCommaSource G) :=
  ⟨innerFibrations.comp_mem _ _ (InnerFibration.mem (q := unitCommaPair G))
    (InnerFibration.mem (q := fst X Y))⟩

/-- 概要：quasicategory 間の関手の comma は quasicategory。
方針：端点の組への inner fibration の底は二つの quasicategory の積。
規約：G の fibration 性は要求しない。
使われ方：普遍矢印の始対象性を comma 内で扱う。 -/
instance unitComma_quasicategory {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (G : Y ⟶ X) : Quasicategory (unitComma G) := by
  let : Quasicategory (X ⊗ Y) := quasicategory_of_innerFibration (fst X Y)
  exact quasicategory_of_innerFibration (unitCommaPair G)

/-- 概要：a→G∘b のホモトピーは comma に値を持つ図式を定める。
方針：ホモトピーを区間の関手へ curry し、境界条件で引き戻しへ持ち上げる。
規約：A の quasicategory 性は不要。
使われ方：単位のホモトピー代表から切断を構成する。 -/
noncomputable def unitCommaLift {A X Y : SSet.{u}} (G : Y ⟶ X)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy a (b ≫ G)) : A ⟶ unitComma G :=
  pullback.lift (curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h)) (lift a b) (by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_natural_left]
    simp only [unitCommaBoundary, uncurry_curry]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality, lift_fst]
    have hb : lift a b ≫ (snd X Y ≫ G) = b ≫ G := by
      rw [← Category.assoc, lift_snd]
    rw [hb]
    have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ (β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h = a := H.h₀
    have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ (β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h = b ≫ G := H.h₁
    have hBoundary : (boundary 1).ι ▷ A ≫ ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram a (b ≫ G) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict, h₀, h₁]
    simpa only [Category.assoc] using hBoundary)

/-- 概要：持ち上げの矢印は元のホモトピーを curry した図式。
方針：引き戻しの持ち上げの第一射影の公式。
規約：ホモトピーの区間を第一因子へ交換する。
使われ方：単位の類を保つことの計算。 -/
lemma unitCommaLift_arrow {A X Y : SSet.{u}} (G : Y ⟶ X)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy a (b ≫ G)) :
    unitCommaLift G a b H ≫ unitCommaArrow G =
      curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h) :=
  pullback.lift_fst _ _ _

/-- 概要：comma への持ち上げの端点の組は指定した (a,b)。
方針：引き戻しの持ち上げの第二射影の公式。
規約：厳密な射の等式。
使われ方：単位の切断の二つの射影の計算。 -/
lemma unitCommaLift_pair {A X Y : SSet.{u}} (G : Y ⟶ X)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy a (b ≫ G)) :
    unitCommaLift G a b H ≫ unitCommaPair G = lift a b :=
  pullback.lift_snd _ _ _

/-- 概要：comma への持ち上げは始域 a の上にある。
方針：端点の組への射影と第一射影を計算する。
規約：厳密な等式。
使われ方：単位から得る切断の条件。 -/
lemma unitCommaLift_source {A X Y : SSet.{u}} (G : Y ⟶ X)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy a (b ≫ G)) :
    unitCommaLift G a b H ≫ unitCommaSource G = a := by
  rw [unitCommaSource, ← Category.assoc, unitCommaLift_pair, lift_fst]

/-- 概要：comma への持ち上げの Y 値の標的は b。
方針：端点の組への射影と第二射影を計算する。
規約：厳密な等式。
使われ方：単位から指定関手 F の回収。 -/
lemma unitCommaLift_target {A X Y : SSet.{u}} (G : Y ⟶ X)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy a (b ≫ G)) :
    unitCommaLift G a b H ≫ unitCommaTarget G = b := by
  rw [unitCommaTarget, ← Category.assoc, unitCommaLift_pair, lift_snd]

/-- 概要：指定単位のホモトピー代表が与える comma の切断。
方針：id→G∘F の代表を comma へ持ち上げる。
規約：η の普遍性は要求しない。
使われ方：各点の条件から普遍矢印への局所存在判定の出発点。 -/
noncomputable def unitCommaSection {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) : X ⟶ unitComma G :=
  unitCommaLift G (𝟙 X) F (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η)

/-- 概要：指定単位の図式は comma の始域射影の厳密な切断。
方針：一般の持ち上げの始域公式を使う。
規約：ホモトピーまででなく射の等式。
使われ方：普遍矢印の部分への制限後も指定関手を保つ。 -/
lemma unitCommaSection_source {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) :
    unitCommaSection η ≫ unitCommaSource G = 𝟙 X :=
  unitCommaLift_source _ _ _ _

/-- 概要：指定単位の切断の標的関手は元の F。
方針：一般の持ち上げの標的公式を使う。
規約：F を別の同値な関手へ置き換えていない。
使われ方：局所存在から指定された随伴対へ戻す。 -/
lemma unitCommaSection_target {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) :
    unitCommaSection η ≫ unitCommaTarget G = F :=
  unitCommaLift_target _ _ _ _

/-- 概要：comma の始域 x 上の fiber。
方針：始域射影の頂点 fiber を取る。
規約：矢印の始点を厳密に x に固定する。
使われ方：普遍矢印をこの fiber の始対象として認識する。 -/
noncomputable def unitCommaFiber {X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (unitCommaSource G) x

/-- 概要：固定始域の comma fiber は quasicategory。
方針：始域射影の inner fibration 性と一般の fiber の定理。
規約：G の始域・標的は quasicategory。
使われ方：fiber 内の始対象の条件を用いる。 -/
instance unitCommaFiber_quasicategory {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (G : Y ⟶ X) (x : X _⦋0⦌) : Quasicategory (unitCommaFiber G x) := by
  unfold unitCommaFiber
  infer_instance

/-- 概要：指定単位の切断の x 成分を始域 x の fiber の頂点として取る。
方針：切断の射影の等式を零単体に適用する。
規約：元の X の頂点 x を底として保つ。
使われ方：各点の単位の普遍矢印としての始対象条件。 -/
noncomputable def unitCommaSectionVertex {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) :
    (unitCommaFiber G x) _⦋0⦌ :=
  ⟨(unitCommaSection η).app (Opposite.op ⦋0⦌) x, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (unitCommaSection_source η) (Opposite.op ⦋0⦌)) x⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.4.7.12" (partial := component) "仮定：準圏間の G:Y→X（HTT と一致）。結論：unitCommaSource は同じ Fun(Δ1,X)×Fun({1},X)Y の始端射影であり、innerFibration と全ての指定終点の Cartesian lifts は CartesianFibration の構造を与える。また Y への像が可逆なら Cartesian。原典の最初の assertion と iff の十分方向に一致し、必要方向は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource_innerFibration
