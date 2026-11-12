module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeGradedInclusion
public import SerrePositivity.KST.Spectra.StrictEnrichedTransformationNerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.NerveFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory
public import SerrePositivity.KST.Spectra.SpectrumIntegerHomotopyDetection

/-!
概要：元の補助単位の相対 BF 左因子を全図式の同型へ移す。
方針：全 Hom 上で証明した厳密自然性と各段の実 π 同型を適用する。
規約：nativeLoop との比較はこの工程に含めない。
使われ方：相対 BF 置換の選択と元の指定左因子を保つ coherent な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance (X Y : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom X Y) :=
  mappingSpace_kanComplex X Y

/-- 概要：相対 BF の可換な組の coherent nerve から元の Sp への射影。
方針：元の対象への全 Hom 豊穣射影を coherent nerve へ写す。
規約：全単体上の実関手。
使われ方：元の Sp と可換な組の同値比較。 -/
def originalInfinityMap : SimplicialNerve Object ⟶ Sp.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap originalEnriched

/-- 概要：元の Sp への射影は元の全 Hom を完全忠実に回収する。
方針：全 Hom の実射影の同値を coherent nerve の判定へ適用する。
規約：点ごとの対象比較だけを用いない。
使われ方：共通の可換解像から元の Sp への同値。 -/
lemma originalInfinityMap_isFullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful originalInfinityMap := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.coherentNerveMap_isFullyFaithful_iff originalEnriched).mpr
  intro X Y
  exact (originalEquivalence X.val Y.val).isQCatEquivalence

/-- 概要：可換な組の射影は元の全 BF 対象を表す。
方針：同じ対象を包んで元の頂点を厳密に回収する。
規約：代表対象の追加条件を仮定しない。
使われ方：元の Sp への実同値の本質的全射性。 -/
lemma originalInfinityMap_isEssentiallySurjective :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective originalInfinityMap := by
  intro y
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y⟩ : Object), ?_⟩
  change Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap originalEnriched).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _)) y)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
  exact ⟨eqToIso (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object y))⟩

/-- 概要：元の射影を順方向とする可換解像と Sp の実同値。
方針：全 Hom の完全忠実性と同じ対象の回収を組み合わせる。
規約：選択した対象ごとの持ち上げの関手性を仮定しない。
使われ方：相対 BF 置換の全図式比較の共通始域。 -/
def originalInfinityEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (SimplicialNerve Object) Sp.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.qCatEquivalenceOfFullyFaithfulEssentiallySurjective originalInfinityMap
    originalInfinityMap_isFullyFaithful originalInfinityMap_isEssentiallySurjective

/-- 概要：指定した相対左因子の非基点側は元の BF 射の頂点そのもの。
方針：全段の評価と curry' の頂点表示を照合する。
規約：coherent 比較の成分を別の辺へ変えない。
使われ方：全図式比較の指定左因子の回収。 -/
lemma inclusionPoint_underlying (X : OmegaSpectrum.{u}) :
    PointedSimplicialSet.forgetUnit ≫ (inclusionPoint X).right =
      vertexOfHomMap (inclusion X) := by
  apply RawSpectrumMapping.hom_ext X (middle X).toKanSequence
  intro n
  change (PointedSimplicialSet.forgetUnit ≫ (inclusionPoint X).right) ≫
      (RawSpectrumMapping.pointedEvaluation X (middle X).toKanSequence n).right = _
  rw [Category.assoc, ← Under.comp_right]
  change PointedSimplicialSet.forgetUnit ≫
      (RawSpectrumMapping.homPoint X (middle X).toKanSequence
        ⟨(inclusion X).app, (inclusion X).comm⟩ ≫
          RawSpectrumMapping.pointedEvaluation X (middle X).toKanSequence n).right = _
  rw [RawSpectrumMapping.homPoint_evaluation]
  change PointedSimplicialSet.forgetUnit ≫
    (MonoidalClosed.curry' ((inclusion X).app n)).right =
      vertexOfHomMap (inclusion X) ≫ evaluation X (middle X) n
  rw [vertexOfHomMap_evaluation, PointedSimplicialSet.forgetUnit_comp]
  rfl

/-- 概要：単体的豊穣自然変換の成分は指定した元の相対 BF 左因子。
方針：単位の非基点側の厳密照合を使う。
規約：成分の辺を同じホモトピー類の別の辺へ変更しない。
使われ方：全図式比較の端点・成分の回収。 -/
lemma gradedInclusion_app (X : Object) :
    gradedInclusion.app X = vertexOfHomMap (inclusion X.val) :=
  inclusionPoint_underlying X.val

/-- 概要：coherent 自然変換から回収した通常の成分射も元の左因子。
方針：元の豊穣 Hom の頂点と通常の射の同値を打ち消す。
規約：各段の射まで同一に保つ。
使われ方：実 π 同型による全図式同型の認証。 -/
lemma componentHom_eq (X : Object) :
    StrictEnrichedTransformation.componentHom originalEnriched replacedEnriched
      gradedInclusion X = inclusion X.val := by
  apply (SimplicialCategory.homEquiv' _ _).injective
  change (SimplicialCategory.homEquiv' _ _)
    ((SimplicialCategory.homEquiv' _ _).symm
      ((gradedInclusion.app X).app _ PUnit.unit)) = _
  rw [Equiv.apply_symm_apply, gradedInclusion_app]
  change vertexOfHom (inclusion X.val) =
    (SSet.unitHomEquiv _) ((SSet.unitHomEquiv _).symm (vertexOfHom (inclusion X.val)))
  exact (Equiv.apply_symm_apply _ _).symm

/-- 概要：指定した相対 BF 左因子を保つ二射影の全図式 FunctorIso。
方針：全 Hom の厳密自然性と元の左因子の実 π 同型を使う。
規約：対象ごとの比較だけから全図式同型を結論しない。
使われ方：補助単位の相対 BF 置換と元の源の coherent な比較。 -/
def inclusionFunctorIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap originalEnriched) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap replacedEnriched) :=
  StrictEnrichedTransformation.functorIso originalEnriched replacedEnriched gradedInclusion
    (fun X ↦ by
      rw [componentHom_eq]
      exact isInvertible_of_piIsomorphism (inclusion X.val)
        (piIsomorphism_of_levelwise _ (inclusion_levelwise X.val)))

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
