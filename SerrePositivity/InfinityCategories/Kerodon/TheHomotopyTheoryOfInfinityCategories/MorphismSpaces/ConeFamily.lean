module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerFiber
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeTerminal
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：錐の関手単体集合での表示と slice からの比較。
方針：join と直積の比較で普遍錐を curry し、図式の固定条件から制限写像の fiber へ移す。
規約：既存の slice と異なる模型との比較射を追加する。
使われ方：Kerodon Example 4.6.6.8（Tag 04J5）、Proposition 7.1.6.13（Tag 02XB）、§7.1.8（Tag 02X8）。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：射を表す関手頂点を uncurry すると、零単体の因子を忘れた元の射。
方針：各次数の評価を計算する。
規約：直積の第一因子は射の始域。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.6.6（Tag 04HY） の頂点での比較。 -/
lemma uncurry_yoneda_functorVertex {A X : SSet.{u}} (f : A ⟶ X) :
    uncurry (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) = fst A (Δ[0] : SSet.{u}) ≫ f := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, t⟩
  dsimp [uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex]
  rfl

/-- 概要：錐の形から図式への関手単体集合の制限射。
方針：右包含で前合成する内部 Hom の射を使う。
規約：錐の形は Δ[0]⋆J。
使われ方：Kerodon Proposition 7.1.6.13（Tag 02XB） の絶対極限の場合。 -/
def coneRestriction (J X : SSet.{u}) :
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J)).obj X ⟶ (ihom J).obj X :=
  (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] J)).app X

/-- 概要：固定図式上の錐の関手単体集合での fiber 表示。
方針：錐の制限射の図式の頂点上の厳密な fiber を取る。
規約：高次単体でも図式を厳密に固定する。
使われ方：Kerodon Example 4.6.6.8（Tag 04J5） の比較の標的。 -/
@[kerodon 04J5]
def coneFamily {J X : SSet.{u}} (p : J ⟶ X) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (coneRestriction J X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)

/-- 概要：錐の制限射は標的が quasicategory なら inner fibration。
方針：右包含の単射性と内部 Hom の制限の内ホーン持ち上げを使う。
規約：添字の単体集合 J は任意。
使われ方：Kerodon Proposition 7.1.6.13（Tag 02XB） の相対終対象の判定。 -/
instance coneRestriction_innerFibration (J X : SSet.{u}) [Quasicategory X] :
    InnerFibration (coneRestriction J X) := by
  unfold coneRestriction
  infer_instance

/-- 概要：固定図式上の関手単体集合による錐の fiber は quasicategory。
方針：錐の制限射の inner fibration 性を使う。
規約：標的 X の quasicategory 性を仮定する。
使われ方：Kerodon Example 4.6.6.8（Tag 04J5） の比較の標的の圏構造。 -/
instance coneFamily_quasicategory {J X : SSet.{u}} [Quasicategory X] (p : J ⟶ X) :
    Quasicategory (coneFamily p) := by
  unfold coneFamily
  infer_instance

/-- 概要：join の錐と関手単体集合による錐の fiber の頂点は同値。
方針：内部 Hom の頂点と実際の射の同値を固定条件に制限する。
規約：比較するのは零単体であり、高次単体の同型は主張しない。
使われ方：Kerodon Example 4.6.6.8（Tag 04J5） の比較の対象の表示。 -/
def coneFamilyVertexEquiv {J X : SSet.{u}} (p : J ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p ≃ (coneFamily p) _⦋0⦌ where
  toFun c := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val, by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] J ≫ c.val) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) 0
    rw [c.property, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]⟩
  invFun c :=
    let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J) X).symm c.val
    ⟨F, by
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
      have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = c.val :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J) X).apply_symm_apply c.val
      have hc : (coneRestriction J X).app (Opposite.op ⦋0⦌) c.val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p :=
        c.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _)
      calc
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] J ≫ F) =
            (coneRestriction J X).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) := rfl
        _ = (coneRestriction J X).app (Opposite.op ⦋0⦌) c.val := congrArg _ hF
        _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p := hc⟩
  left_inv c := by
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J) X).symm_apply_apply c.val
  right_inv c := by
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J) X).apply_symm_apply c.val

/-- 概要：slice の普遍錐を錐の形と slice の直積上の射にする。
方針：直積のパラメーターを join の左因子へ移す比較を使う。
規約：直積では錐の形を第一因子とする。
使われ方：Kerodon Construction 4.6.6.4（Tag 04J1） の比較射の uncurry。 -/
noncomputable def sliceConeFamilyUncurry {J X : SSet.{u}} (p : J ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p ⟶ X :=
  (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) Δ[0] J ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) Δ[0]) (𝟙 J) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p))

/-- 概要：直積上の普遍錐は右因子の図式上で固定される。
方針：比較射の右包含上の計算と slice の普遍性の固定条件を使う。
規約：右図式上では slice のパラメーターを忘れる。
使われ方：Kerodon Example 4.6.6.8（Tag 04J5） の fiber 条件。 -/
lemma sliceConeFamilyUncurry_fixed {J X : SSet.{u}} (p : J ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] J ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) ≫ sliceConeFamilyUncurry p = fst J (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) ≫ p := by
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p
  have hswap : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] J ▷ S) ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J) S).hom =
      (β_ J S).hom ≫ (S ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] J) := rfl
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] J ▷ S) ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J) S).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft S Δ[0] J ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (fst S Δ[0]) (𝟙 J) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (𝟙 S) = _
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] J ▷ S), hswap]
  simp only [Category.assoc]
  rw [← Category.assoc (S ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] J), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft_inr]
  simp only [Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (S ⊗ Δ[0]) J), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed]
  rfl

/-- 概要：普遍錐を curry した射は、制限後に図式の頂点に定値となる。
方針：uncurry して右図式上の固定条件を比較する。
規約：定値射は内部 Hom の図式の頂点を値とする。
使われ方：Kerodon Example 4.6.6.8（Tag 04J5） の比較射を fiber に持ち上げる条件。 -/
lemma sliceConeFamilyUncurry_curry_fixed {J X : SSet.{u}} (p : J ⟶ X) :
    curry (sliceConeFamilyUncurry p) ≫ coneRestriction J X = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) := by
  apply uncurry_injective
  rw [coneRestriction, uncurry_pre_app, uncurry_curry, sliceConeFamilyUncurry_fixed]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨j, c⟩
  dsimp [uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex]
  rfl

/-- 概要：join で定義した slice を関手単体集合の錐の fiber へ比較する。
方針：普遍錐の curry を、制限後の固定条件によって fiber へ持ち上げる。
規約：既存の slice の定義は変更しない。
使われ方：Kerodon Example 4.6.6.8（Tag 04J5） の同値の候補射。 -/
noncomputable def sliceConeFamilyMap {J X : SSet.{u}} (p : J ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p ⟶ coneFamily p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (coneRestriction J X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)
    (curry (sliceConeFamilyUncurry p)) (sliceConeFamilyUncurry_curry_fixed p)

/-- 概要：slice の指定された錐に普遍族を制限すると、その錐に定値な族。
方針：直積と join の比較のパラメーターへの自然性と一点での計算を使う。
規約：パラメーターは標準零単体。
使われ方：Kerodon Example 4.6.6.8（Tag 04J5） の比較射の零単体。 -/
lemma sliceConeFamilyUncurry_vertex {J X : SSet.{u}} (p : J ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J ◁ SSet.yonedaEquiv.symm c) ≫ sliceConeFamilyUncurry p =
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J) (Δ[0] : SSet.{u}) ≫ c.val := by
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) J
  let v : (Δ[0] : SSet.{u}) ⟶ S := SSet.yonedaEquiv.symm c
  have hswap : (T ◁ v) ≫ (β_ T S).hom = (β_ T Δ[0]).hom ≫ (v ▷ T) := rfl
  have hv : (v ▷ (Δ[0] : SSet.{u})) ≫ fst S Δ[0] = snd Δ[0] Δ[0] ≫ v := by
    change fst (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ v = snd Δ[0] Δ[0] ≫ v
    exact congrArg (fun j ↦ j ≫ v) (stdSimplex.isTerminalObj₀.hom_ext _ _)
  have hjoin : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (v ▷ (Δ[0] : SSet.{u})) (𝟙 J) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (fst S Δ[0]) (𝟙 J) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (snd (Δ[0] : SSet.{u}) Δ[0]) (𝟙 J) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap v (𝟙 J) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, hv]
  have hvF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap v (𝟙 J) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (𝟙 S) = c.val := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, Category.comp_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda 0 c
  change (T ◁ v) ≫ (β_ T S).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft S Δ[0] J ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (fst S Δ[0]) (𝟙 J) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (𝟙 S) = _
  rw [← Category.assoc (T ◁ v), hswap]
  simp only [Category.assoc]
  rw [← Category.assoc (v ▷ T), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (v ▷ (Δ[0] : SSet.{u})) (𝟙 J)), hjoin]
  simp only [Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft (Δ[0] : SSet.{u}) Δ[0] J), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft_unit]
  change fst T (Δ[0] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap v (𝟙 J) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (𝟙 S) = _
  rw [hvF]

/-- 概要：slice から錐の fiber への比較の零次成分は錐の標準的な頂点表示。
方針：Yoneda の逆で比較し、curry と直積上の普遍族の零単体での計算を使う。
規約：高次での同値性はこの補題には含まない。
使われ方：Kerodon Example 4.6.6.8（Tag 04J5） の極限錐の頂点の同定。 -/
lemma sliceConeFamilyMap_app_zero {J X : SSet.{u}} (p : J ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    (sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) c = coneFamilyVertexEquiv p c := by
  apply Subtype.ext
  change (curry (sliceConeFamilyUncurry p)).app (Opposite.op ⦋0⦌) c = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_comp, ← curry_natural_left, sliceConeFamilyUncurry_vertex]
  apply uncurry_injective
  rw [uncurry_curry, uncurry_yoneda_functorVertex]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
