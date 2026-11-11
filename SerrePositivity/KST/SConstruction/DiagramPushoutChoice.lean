module
public import SerrePositivity.KST.SConstruction.JointNormalizedPushoutSection
public import SerrePositivity.KST.SConstruction.GappedPushoutPreservation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.InternalHomFlipAdjunction

/-! # 図式圏での正規化した関手的押し出し
概要：一つの正規化した選択を任意の図式圏へ移し、添字制限との厳密な両立を示す。
方針：span の族に選択を後合成し、内部 Hom の二変数を交換する。
規約：図式圏ごとに別の切断を選ばない。使われ方：Fiore–Pieper Corollary 3.35、McCarthy の単体恒等式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：二変数の図式を交換した後の評価は元の族の指定頂点を表す。
方針：内部 Hom の交換と評価の可換性を関手頂点の同値で戻す。
規約：始域・標的の quasicategory 性は不要。使われ方：選んだ図式の点ごとの普遍性。 -/
lemma flipFamily_evaluate {K A C : SSet.{u}} (F : K ⟶ (ihom A).obj C) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K A C F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C).symm (F.app (Opposite.op ⦋0⦌) k) := by
  have he := congrArg (fun q => q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_evaluate K A C k)
  change ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) k)).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K A C).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C).injective
  rw [Equiv.apply_symm_apply]
  exact he

/-- 概要：同時正規化した切断の実際の普遍四角形の族。
方針：押し出し全部分複体の包含を後合成する。
規約：全 span の内部 Hom 上の一つの単体的射。使われ方：任意の図式圏で共通に使う選択。 -/
def normalizedPushoutSquareChoice (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    (ihom (horn 2 0 : SSet.{u})).obj C ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C :=
  jointNormalizedPushoutSection C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsPushoutDiagramVertex).ι

/-- 概要：選んだ四角形の族は入力 span を厳密に回収する。
方針：正規化した切断の射影の式。
規約：単体的射の等号。使われ方：図式圏での押し出しの二辺の回収。 -/
lemma normalizedPushoutSquareChoice_span (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    normalizedPushoutSquareChoice C ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C = 𝟙 _ :=
  (Category.assoc _ _ _).trans (jointNormalizedPushoutSection_projection C)

/-- 概要：選んだ四角形の族は両向きの恒等 span 上で標準四角形を回収する。
方針：同時正規化の式に全部分複体の包含を後合成する。
規約：同じ選択が両向きの条件を満たす。使われ方：単体ホモトピーの端点の厳密な照合。 -/
lemma normalizedPushoutSquareChoice_identity (b : Bool) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    identitySpanFamily b C ≫ normalizedPushoutSquareChoice C =
      (pre (identityPushoutShape b)).app C := by
  rw [normalizedPushoutSquareChoice, ← Category.assoc,
    jointNormalizedPushoutSection_identity, identityPushoutFamily_ι]

/-- 概要：任意のパラメーターを持つ span の族に同じ選択を適用する。
方針：固定した普遍四角形の射を後合成する。
規約：パラメーターには条件を課さない。使われ方：点ごとの押し出しの図式。 -/
def chosenPushoutFamily {K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (d : K ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) :
    K ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C := d ≫ normalizedPushoutSquareChoice C

/-- 概要：任意の図式圏で点ごとの同じ選択による押し出し四角形。
方針：選んだ四角形の族の二変数を交換する。
規約：図式圏で新たな切断を選ばない。使われ方：McCarthy のパラメーター付き押し出し。 -/
def chosenDiagramPushout {K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (d : K ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) :
    (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom K).obj C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K (Δ[1] ⊗ Δ[1]) C (chosenPushoutFamily d)

/-- 概要：図式圏で選んだ押し出しの入力は元の span の族。
方針：内部 Hom の交換と形状制限の自然性を使う。
規約：同型による回収ではなく等号。使われ方：指定した入力の普遍的な補完。 -/
lemma chosenDiagramPushout_span {K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (d : K ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ chosenDiagramPushout d = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K _ C d := by
  rw [chosenDiagramPushout, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, chosenPushoutFamily,
    Category.assoc, normalizedPushoutSquareChoice_span, Category.comp_id]

/-- 概要：図式圏で選んだ四角形は実際に押し出し。
方針：全頂点で選択した普遍四角形を評価し、関手圏の点ごとの判定を適用する。
規約：有限性や追加の span の存在仮定は不要。使われ方：McCarthy 法の図式圏での普遍性。 -/
lemma chosenDiagramPushout_isPushout {K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (d : K ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (chosenDiagramPushout d) := by
  apply (functor_pushout_iff_pointwise _).2
  intro k
  rw [chosenDiagramPushout, flipFamily_evaluate]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
    ((d ≫ jointNormalizedPushoutSection C).app (Opposite.op ⦋0⦌) k)

/-- 概要：点ごとの押し出しの選択は添字の任意の制限と厳密に両立する。
方針：固定した選択への後合成と内部 Hom の交換の自然性。
規約：面・退化の両方を含む。使われ方：McCarthy の単体恒等式。 -/
lemma chosenDiagramPushout_reindex {K L C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (i : L ⟶ K) (d : K ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) :
    chosenDiagramPushout (i ≫ d) = chosenDiagramPushout d ≫ (pre i).app C := by
  dsimp only [chosenDiagramPushout, chosenPushoutFamily]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre]

/-- 概要：図式圏で選ぶ押し出しは両向きの恒等 span で標準四角形を厳密に回収する。
方針：正規化した選択と内部 Hom の交換の形状制限の式を使う。
規約：任意のパラメーターを持つ族についての等号。使われ方：ホモトピーの退化と端点。 -/
lemma chosenDiagramPushout_identity {K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (b : Bool) (g : K ⟶ (ihom (Δ[1] : SSet.{u})).obj C) :
    chosenDiagramPushout (g ≫ identitySpanFamily b C) =
      identityPushoutShape b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K _ C g := by
  dsimp only [chosenDiagramPushout, chosenPushoutFamily]
  rw [Category.assoc, normalizedPushoutSquareChoice_identity, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]

/-- 概要：図式圏の任意の指定 span に正規化した押し出し四角形を選ぶ。
方針：入力を点ごとの span の族へ交換し、同じ選択を適用する。
規約：入力は実際の図式圏の span。使われ方：図式圏での普遍的な補完の直接の API。 -/
def selectedFunctorPushout {K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (p : (horn 2 0 : SSet.{u}) ⟶ (ihom K).obj C) :
    (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom K).obj C :=
  chosenDiagramPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (horn 2 0) K C p)

/-- 概要：図式圏で選んだ普遍四角形は指定 span を厳密に保持する。
方針：族の span の式と内部 Hom の交換の逆律。
規約：指定した二辺を取り替えない。使われ方：McCarthy 法の固定された入力の補完。 -/
lemma selectedFunctorPushout_span {K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (p : (horn 2 0 : SSet.{u}) ⟶ (ihom K).obj C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (selectedFunctorPushout p) = p := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ chosenDiagramPushout _ = p
  rw [chosenDiagramPushout_span]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (horn 2 0) K C).symm_apply_apply p

/-- 概要：指定 span の選択した四角形は図式圏の押し出し。
方針：点ごとの族から構成した押し出しの普遍性。
規約：任意の添字と任意の span。使われ方：McCarthy 法の普遍的な押し出し。 -/
lemma selectedFunctorPushout_isPushout {K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (p : (horn 2 0 : SSet.{u}) ⟶ (ihom K).obj C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (selectedFunctorPushout p) :=
  chosenDiagramPushout_isPushout _

/-- 概要：図式圏の指定 span の押し出しの選択は任意の添字制限と厳密に両立する。
方針：入力の二変数の交換と点ごとの選択の添字制限の式を使う。
規約：同じ選択が全ての面・退化に適用される。使われ方：McCarthy の単体恒等式。 -/
lemma selectedFunctorPushout_reindex {K L C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (i : L ⟶ K) (p : (horn 2 0 : SSet.{u}) ⟶ (ihom K).obj C) :
    selectedFunctorPushout (p ≫ (pre i).app C) = selectedFunctorPushout p ≫ (pre i).app C := by
  dsimp only [selectedFunctorPushout]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, chosenDiagramPushout_reindex]

end SerrePositivity.KST.SConstruction
