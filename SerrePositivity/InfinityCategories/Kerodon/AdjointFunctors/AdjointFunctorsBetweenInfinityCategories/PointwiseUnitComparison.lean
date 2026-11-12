module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantUnitFormula
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.PinchedObjectNaturality

/-!
概要：指定単位による各点の実際の写像空間比較と、随伴からの比較の照合。
方針：G の作用の後に単位成分で前合成し、族の Hom 表示で認識する。
規約：各点の比較を定義する段階では随伴の存在は要求しない。
使われ方：Kerodon Cor 6.2.6.5（Tag 02FX） の各点の条件の正確な型。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：指定単位による各点の区間模型の比較。
方針：G で後合成し、単位の x 成分で前合成する。
規約：η は任意の h Fun の射でよい。
使われ方：各点の単位条件を実際の写像空間の射で述べる。 -/
noncomputable def unitIntervalMap {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap G (F.app (Opposite.op ⦋0⦌) x) y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (G.app (Opposite.op ⦋0⦌) y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent η x)

/-- 概要：指定単位の比較射は任意の族で定値関手間の単位比較を表す。
方針：後合成・前合成の族の公式と各点の単位成分の式を合わせる。
規約：パラメータ A は quasicategory。端点 x,y は固定。
使われ方：標準の単位比較と adjunct 比較を同定する。 -/
lemma unitIntervalMap_family {A X Y : SSet.{u}} [Quasicategory A]
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ unitIntervalMap η x y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantUnitHomMap η A x y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom f) := by
  rw [unitIntervalMap, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_family,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorMap_familyHom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantUnitHomMap_formula]

/-- 概要：随伴の単位による標準比較は既存の区間 adjunct 比較にホモトピック。
方針：普遍族で両者が同じ adjunct を表すことを確認する。
規約：実際の単体的ホモトピーを返す。
使われ方：Cor 6.2.6.5 の (1) から (2) の標準比較との照合。 -/
lemma QCatAdjunction.unitIntervalMap_homotopy {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    Nonempty (SSet.Homotopy (unitIntervalMap a.unitHom x y) (a.intervalMap x y)) := by
  apply a.intervalMap_unique_homotopy x y
  have h := unitIntervalMap_family a.unitHom x y (𝟙 _)
  simpa only [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantUnitHomMap_of_adjunction] using h

/-- 概要：随伴の単位による標準の区間比較はホモトピー同値。
方針：既存の adjunct 比較の同値性を上のホモトピーで移す。
規約：写像空間は Kan 複体。
使われ方：指定単位の各点の写像空間判定の順方向。 -/
lemma QCatAdjunction.unitIntervalMap_isSimplicialHomotopyEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (unitIntervalMap a.unitHom x y) :=
  ((a.intervalMap_isSimplicialHomotopyEquivalence x y).isQCatEquivalence.ofFunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (a.unitIntervalMap_homotopy x y).some).symm
  ).isSimplicialHomotopyEquivalence

/-- 概要：指定単位による標準比較を右 pinched 模型で述べる射。
方針：区間模型の標準比較を模型比較とその逆で移す。
規約：既存の PinchedInterval の比較の選択を使う。
使われ方：各点の条件を当初の pinchedHom の型で述べる。 -/
noncomputable def unitPinchedMap {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (F.app (Opposite.op ⦋0⦌) x) y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x (G.app (Opposite.op ⦋0⦌) y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.liftMap (unitIntervalMap η x y)

/-- 概要：標準 pinched 比較は G の作用の後の単位成分による前合成。
方針：模型比較の標的の射に関する自然性を使う。
規約：Cor 6.2.6.5 の合成の順序と一致する。
使われ方：標準比較の原典との対応を指定する。 -/
lemma unitPinchedMap_formula {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    unitPinchedMap η x y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap G (F.app (Opposite.op ⦋0⦌) x) y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose (G.app (Opposite.op ⦋0⦌) y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent η x) := by
  simpa only [unitPinchedMap, unitIntervalMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.liftMap, Category.assoc] using
    congrArg (fun q ↦ q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (G.app (Opposite.op ⦋0⦌) y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent η x) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x
          (G.app (Opposite.op ⦋0⦌) y)).choose.inv)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.pinchedIntervalComparison_naturality G (F.app (Opposite.op ⦋0⦌) x) y).symm

/-- 概要：随伴の単位の標準 pinched 比較は既存の adjunct 比較と同型。
方針：区間模型でのホモトピーを移し、既存の比較の指定射と照合する。
規約：h Fun の同型として述べる。
使われ方：標準単位による比較が既存の自然な同値を表すことの認識。 -/
noncomputable def QCatAdjunction.unitPinchedMapIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (unitPinchedMap a.unitHom x y) (a.pinchedMap x y) := by
  rw [a.pinchedMap_eq_liftMap]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.liftMapIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (a.unitIntervalMap_homotopy x y).some)

/-- 概要：指定単位による各点の pinched 写像空間条件。
方針：標準比較の全ての x,y での実際のホモトピー逆の存在を要求する。
規約：定義には全パラメータ A の条件を追加しない。
使われ方：Cor 6.2.6.5 の各点の条件。これから随伴への逆方向は別工程。 -/
def UnitMappingSpaceCondition {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) : Prop :=
  ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (unitPinchedMap η x y)

/-- 概要：模型比較による射の移送は同値性を保存し反映する。
方針：始域の比較と終域の比較の逆が同値であることを使い、両端を相殺する。
規約：固定した端点の間の任意の区間模型の射。
使われ方：単位の各点の条件を区間模型へ戻す。 -/
lemma PinchedInterval.liftMap_isQCatEquivalence_iff {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.liftMap f) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f := by
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x₀ x₁
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence y₀ y₁).choose.symm.isQCatEquivalence
  constructor
  · intro h
    exact ht.cancel_right (hs.cancel_left h)
  · intro h
    exact hs.comp (h.comp ht)

/-- 概要：指定単位の各点の条件は pinched 模型と区間模型で同値。
方針：模型の移送による同値性の保存・反映と Kan 複体の比較を使う。
規約：どちらも全ての x,y の実際のホモトピー同値性を要求する。
使われ方：逆方向の局所存在の証明で模型を選ぶ。 -/
lemma unitMappingSpaceCondition_iff_interval {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) :
    UnitMappingSpaceCondition η ↔ ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (unitIntervalMap η x y) := by
  constructor
  · intro h x y
    exact ((PinchedInterval.liftMap_isQCatEquivalence_iff (unitIntervalMap η x y)).mp
      (h x y).isQCatEquivalence).isSimplicialHomotopyEquivalence
  · intro h x y
    exact ((PinchedInterval.liftMap_isQCatEquivalence_iff (unitIntervalMap η x y)).mpr
      (h x y).isQCatEquivalence).isSimplicialHomotopyEquivalence

/-- 概要：随伴の単位は各点の pinched 写像空間条件を満たす。
方針：既存の pinched adjunct 同値を標準比較との同型で移す。
規約：ここで証明するのは点ごとの条件への順方向。
使われ方：Cor 6.2.6.5 の (1) から (2)。 -/
lemma QCatAdjunction.unitMappingSpaceCondition {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) : UnitMappingSpaceCondition a.unitHom := by
  intro x y
  exact ((a.pinchedMap_isSimplicialHomotopyEquivalence x y).isQCatEquivalence.ofFunctorIso
    (a.unitPinchedMapIso x y).symm).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
