module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.SpaceHomotopyPushouts
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization

/-!
概要：Kan 複体間の任意の射を、Kan な中間対象を経由する単射と trivial Kan fibration に分解する。
方針：境界の小対象論法の確定済みの関手的分解を使い、右因子から中間対象の Kan 性を得る。
規約：単射性と持ち上げ性は台の単体集合の射について主張する。
使われ方：HTT 4.2.4.1、任意の span の一脚を単射に替えて homotopy 押し出しを構成する。

対応節は Kerodon 1.5（Tag 0055）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories
noncomputable section

/-- 概要：Kan な底への trivial Kan fibration の全空間は Kan。
方針：全ホーンに対する持ち上げ性で Kan fibration とし、終対象への射の合成を使う。
規約：全空間の充填性を前提にしない。
使われ方：境界の単射分解の中間対象を Kan 複体として束縛する。 -/
lemma kanComplex_of_trivialKanFibration_target {A B : SSet.{u}} [KanComplex B]
    (p : A ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] : KanComplex A := by
  have : Fibration p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_hasLiftingProperty_horn p (fun n i ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) (horn (n + 1) i).ι inferInstance)
  change Fibration (terminal.from A)
  have h : terminal.from A = p ≫ terminal.from B := terminal.hom_ext _ _
  rw [h]
  infer_instance

variable {A B : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}

/-- 概要：Kan 複体間の射の境界分解の中間対象は Kan 複体。
方針：右因子の全ての単射に対する持ち上げ性と終域の Kan 性を使う。
規約：元の射 f の単射性は不要。
使われ方：任意の span の単射な左脚の新しい終域。 -/
def kanMonoArrowObject (f : A ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} := by
  let q := SerrePositivity.SimplicialModel.MonoLocalizedFactorization.right
    (show A.obj ⟶ B.obj from f)
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q :=
    ⟨SerrePositivity.SimplicialModel.MonoLocalizedFactorization.right_all_mono_rlp f⟩
  exact ⟨_, kanComplex_of_trivialKanFibration_target q⟩

/-- 概要：元の始域から Kan な中間対象への境界分解の左因子。
方針：既存の関手的な分解の実際の左射を使う。
規約：Kan 複体の圏の射として束縛する。
使われ方：homotopy 押し出しへ適用する単射な左脚。 -/
def kanMonoArrowLeft (f : A ⟶ B) : A ⟶ kanMonoArrowObject f :=
  SerrePositivity.SimplicialModel.MonoLocalizedFactorization.left f

/-- 概要：Kan な中間対象から元の終域への境界分解の右因子。
方針：既存の関手的な分解の実際の右射を使う。
規約：元の終域 B を保持する。
使われ方：置換した span から元の span への成分ごとの同値。 -/
def kanMonoArrowRight (f : A ⟶ B) : kanMonoArrowObject f ⟶ B :=
  SerrePositivity.SimplicialModel.MonoLocalizedFactorization.right f

/-- 概要：Kan な中間対象への境界分解の左射は台で単射。
方針：境界の小対象論法の左因子の単射性を使う。
規約：通常の Kan 複体の圏の Mono で代用しない。
使われ方：一脚が単射な span の homotopy 押し出し定理の仮定。 -/
instance kanMonoArrowLeft_mono (f : A ⟶ B) : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.map (kanMonoArrowLeft f)) :=
  SerrePositivity.SimplicialModel.MonoLocalizedFactorization.left_mono f

/-- 概要：境界分解の右射は台の trivial Kan fibration。
方針：全ての単射への右持ち上げ性をそのままクラスへ移す。
規約：射の単位や局所化への像だけではなく実際の射を扱う。
使われ方：置換した span の比較成分の同値性の検証。 -/
instance kanMonoArrowRight_trivialKanFibration (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.map (kanMonoArrowRight f)) :=
  ⟨SerrePositivity.SimplicialModel.MonoLocalizedFactorization.right_all_mono_rlp f⟩

/-- 概要：境界分解の左右の Kan な射の合成は元の射に厳密に一致する。
方針：関手的な分解の因子化の式を使う。
規約：通常の Kan 複体の圏の射の等号。
使われ方：置換前後の span の自然変換の厳密な可換性。 -/
lemma kanMonoArrow_fac (f : A ⟶ B) : kanMonoArrowLeft f ≫ kanMonoArrowRight f = f :=
  SerrePositivity.SimplicialModel.MonoLocalizedFactorization.fac f

/-- 概要：境界分解の右射は元の終域への実際の単体的ホモトピー同値。
方針：両端の Kan 性の下で trivial Kan fibration の同値性を使う。
規約：同値性の結論は台の単体集合の射について述べる。
使われ方：Kan 値図式の成分ごとの比較を coherent な図式の同型へ移す。 -/
lemma kanMonoArrowRight_homotopyEquivalence (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.map (kanMonoArrowRight f)) := by
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.obj (kanMonoArrowObject f)) :=
    inferInstanceAs (KanComplex (kanMonoArrowObject f).obj)
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.obj B) := inferInstanceAs (KanComplex B.obj)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence

end
end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories
