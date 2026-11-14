module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.DerivedGeometry.KInjectiveLocalizationUnit
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
概要：K-injective ホモトピー対象の包含は非有界の右導来構造を与える。
方針：局所化の随伴の単位を関手的な準同型分解として使う。
規約：関手的分解の存在を仮定せず、構成済みの局所化随伴から作る。
使われ方：TT §3・§8、Toën §3.2、Stacks 19.12.6 の非有界右導来関手の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable (C : Type u) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{v} C]

/--
概要：ホモトピー対象を K-injective ホモトピー対象へ関手的に移す。
方針：局所化と構成した右随伴を合成し、右直交性へ制限する。
規約：単位の成分は後で準同型と判定する。
使われ方：TT §3、Toën §3.2 の非有界の関手的分解。
-/
def kInjectiveReplacementFunctor : HomotopyCategory C (.up ℤ) ⥤
    (kInjectiveHomotopyObjects C).FullSubcategory :=
  (kInjectiveHomotopyObjects C).lift
    (DerivedCategory.Qh ⋙ kInjectiveLocalizationRightAdjoint C)
    (fun X => kInjectiveLocalizationObject_rightOrthogonal C (DerivedCategory.Qh.obj X))

/--
概要：K-injective な関手的分解への自然な射。
方針：局所化の随伴の単位を使う。
規約：ホモトピー圏の自然変換。
使われ方：TT §3、Toën §3.2 の右導来構造の分解射。
-/
def kInjectiveReplacementUnit : 𝟭 (HomotopyCategory C (.up ℤ)) ⟶
    kInjectiveReplacementFunctor C ⋙ (kInjectiveHomotopyObjects C).ι :=
  (kInjectiveLocalizationAdjunction C).unit

/--
概要：関手的な K-injective 分解の各成分は準同型。
方針：局所化での単位の同型性と Mathlib の準同型判定を使う。
規約：存在だけでなく構成した自然変換についての主張。
使われ方：TT §3、Toën §3.2 の非有界右導来構造。
-/
lemma kInjectiveReplacementUnit_mem_quasiIso (X : HomotopyCategory C (.up ℤ)) :
    HomotopyCategory.quasiIso C (.up ℤ) ((kInjectiveReplacementUnit C).app X) :=
  (DerivedCategory.isIso_Qh_map_iff _).mp
    (kInjectiveLocalizationAdjunction_map_unit_isIso C X)

/--
概要：K-injective 対象の包含による局所化の射。
方針：包含で引き戻した準同型類を始域の弱同値とする。
規約：始域の弱同値は後で同型に反映される。
使われ方：TT §3、Toën §3.2 の右導来性の判定。
-/
@[implicit_reducible]
def kInjectiveLocalizerMorphism : LocalizerMorphism
    ((HomotopyCategory.quasiIso C (.up ℤ)).inverseImage (kInjectiveHomotopyObjects C).ι)
    (HomotopyCategory.quasiIso C (.up ℤ)) where
  functor := (kInjectiveHomotopyObjects C).ι
  map := by rfl

/-- 概要：局所化の射の包含は完全。方針：充満部分圏の包含を使う。
規約：局所化の前の圏。使われ方：TT §3、Toën §3.2 の導来構造。 -/
instance kInjectiveLocalizerMorphism_functor_full : (kInjectiveLocalizerMorphism C).functor.Full :=
  inferInstanceAs ((kInjectiveHomotopyObjects C).ι.Full)

/-- 概要：局所化の射の包含は忠実。方針：充満部分圏の包含を使う。
規約：局所化の前の圏。使われ方：TT §3、Toën §3.2 の導来構造。 -/
instance kInjectiveLocalizerMorphism_functor_faithful :
    (kInjectiveLocalizerMorphism C).functor.Faithful :=
  inferInstanceAs ((kInjectiveHomotopyObjects C).ι.Faithful)

/--
概要：ホモトピー圏の準同型類は二つから三つの性質を持つ。
方針：導来局所化の同型の逆像として表す。
規約：実際の Mathlib の準同型類。
使われ方：TT §3、Toën §3.2 の右導来構造の構成。
-/
instance homotopyQuasiIso_hasTwoOutOfThree :
    (HomotopyCategory.quasiIso C (.up ℤ)).HasTwoOutOfThreeProperty := by
  have h : HomotopyCategory.quasiIso C (.up ℤ) =
      (MorphismProperty.isomorphisms (DerivedCategory C)).inverseImage DerivedCategory.Qh := by
    ext X Y f
    exact (DerivedCategory.isIso_Qh_map_iff f).symm
  rw [h]
  infer_instance

/--
概要：K-injective 対象の包含は非有界右導来構造。
方針：実際の関手的な準同型分解から、Mathlib の導来構造の構成定理を適用する。
規約：分解の存在を未証明フィールドにしない。
使われ方：TT §3・§8、Toën §3.2 の右導来関手の普遍性。
-/
instance kInjectiveLocalizerMorphism_isRightDerivabilityStructure :
    (kInjectiveLocalizerMorphism C).IsRightDerivabilityStructure :=
  (kInjectiveLocalizerMorphism C).isRightDerivabilityStructure_of_functorial_resolutions
    (kInjectiveReplacementUnit C) (kInjectiveReplacementUnit_mem_quasiIso C) rfl

/--
概要：K-injective 対象の局所化の射は、射の圏でも右分解を持つ。
方針：自然な単位の二つの成分を可換四角形として使う。
規約：射の分解も構成済みの関手的分解から得る。
使われ方：TT §3、Toën §3.2 の三角右導来関手。
-/
instance kInjectiveLocalizerMorphism_arrow_hasRightResolutions :
    (kInjectiveLocalizerMorphism C).arrow.HasRightResolutions :=
  (kInjectiveLocalizerMorphism C).hasRightResolutions_arrow_of_functorial_resolutions
    (kInjectiveReplacementUnit C) (kInjectiveReplacementUnit_mem_quasiIso C)

/--
概要：任意のホモトピー圏の関手は K-injective 右導来構造で導来化できる。
方針：弱同値な K-injective 対象の射は、導来比較の完全忠実性で同型に反映される。
規約：関手の加法性はこの存在判定だけには不要。
使われ方：TT §3、Toën §3.2 の非有界右導来関手。
-/
lemma kInjectiveLocalizerMorphism_derives {E : Type*} [Category* E]
    (F : HomotopyCategory C (.up ℤ) ⥤ E) : (kInjectiveLocalizerMorphism C).Derives F := by
  intro X Y f hf
  have : IsIso ((kInjectiveDerivedFunctor C).map f) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ)) _ hf
  have : IsIso f := isIso_of_reflects_iso f (kInjectiveDerivedFunctor C)
  exact CategoryTheory.Functor.map_isIso ((kInjectiveHomotopyObjects C).ι ⋙ F) f

end SerrePositivity.KST.DerivedGeometry

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.5.13" (partial := special) "仮定：通常の Grothendieck 圏のホモトピー圏、または可換環上の dg 加群（Lean が強い：準圏側は後者のみ）。結論：K-injective 置換の単位が準同型であり、dg 加群では半自由置換が局所化（Lean が弱い：一般の Grothendieck 圏で fibrant 複体の dg nerve が反射部分圏である型はない）。"] _root_.SerrePositivity.KST.DerivedGeometry.kInjectiveReplacementUnit_mem_quasiIso
