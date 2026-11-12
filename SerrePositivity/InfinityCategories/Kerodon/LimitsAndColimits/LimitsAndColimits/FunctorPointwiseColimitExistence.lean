module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseColimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamilies
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InternalHomFlipVertices
public import Mathlib.Tactic.CrossRefAttribute

/-! # 関手圏の余極限の存在と点ごとの判定
概要：各点での余極限の存在から自然な余極限余錐を構成し、任意の余極限余錐が点ごとに普遍となることを示す。
方針：普遍余錐の族の選択と内部 Hom の転置を使い、余錐の一意性で比較する。
規約：Core の公開名・型は変更しない。使われ方：HTT 5.1.2.2 の双対、BGT Lemma 7.3。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：図式の全ての評価が余極限を持つ条件。
方針：各頂点で通常の HasColimit を要求する。
規約：選んだ余錐の自然性は要求しない。使われ方：関手圏の余極限の存在の前提。 -/
def HasPointwiseColimits {J K X : SSet.{u}} (p : J ⟶ (ihom K).obj X) : Prop :=
  ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram p k)

/-- 概要：点ごとに普遍な自然な余錐があれば全評価図式に余極限が存在する。
方針：既存の余錐を各点で評価する。
規約：quasicategory 性を要求しない。使われ方：点ごとの存在条件の回収。 -/
lemma IsPointwiseColimitCone.hasPointwiseColimits {J K X : SSet.{u}}
    {p : J ⟶ (ihom K).obj X} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p} (hc : IsPointwiseColimitCone c) :
    HasPointwiseColimits p := fun k => ⟨evaluateFunctorCocone c k, hc k⟩

/-- 概要：図式の全評価に余極限が存在すれば、自然な点ごとの余極限余錐が存在する。
方針：転置した図式の普遍余錐を族として選び、内部 Hom を再び転置する。
規約：X は quasicategory、J と K は任意。使われ方：HTT 5.1.2.2 の余極限側の存在。 -/
@[kerodon 02XJ]
lemma exists_pointwiseColimitCone {J K X : SSet.{u}} [Quasicategory X]
    (p : J ⟶ (ihom K).obj X) (hp : HasPointwiseColimits p) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, IsPointwiseColimitCone c := by
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u})
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv J K X p
  have hq (k : K _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv J X).symm (q.app (Opposite.op ⦋0⦌) k)) := by
    dsimp only [q]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv J X).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv J X (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram p k)))
    rw [Equiv.symm_apply_apply]
    exact hp k
  obtain ⟨f, hf⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCoconeFamily q hq
  let F : K ⟶ (ihom T).obj X :=
    f ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J X)).ι
  have hFp : F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J X = q := hf
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K T X F
  have hGF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv T K X G = F :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K T X).left_inv F
  have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J (Δ[0] : SSet.{u}) ≫ G = p := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv J K X).injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre, hGF]
    exact hFp
  let c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p := ⟨G, hG⟩
  refine ⟨c, ?_⟩
  intro k
  have hk := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero G k
  rw [hGF] at hk
  change F.app (Opposite.op ⦋0⦌) k = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (evaluateFunctorCocone c k).val at hk
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_initialBoundaryLifting (evaluateFunctorCocone c k)).2
  rw [← hk]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (f.app (Opposite.op ⦋0⦌) k)

/-- 概要：全評価が余極限を持つ図式は関手圏で余極限を持つ。
方針：点ごとの自然な余極限余錐を構成して関手圏の判定を使う。
規約：X は quasicategory。使われ方：パラメーターを保った cofiber の普遍性。 -/
@[kerodon 05QG]
lemma hasColimit_of_hasPointwiseColimits {J K X : SSet.{u}} [Quasicategory X]
    (p : J ⟶ (ihom K).obj X) (hp : HasPointwiseColimits p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p := by
  obtain ⟨c, hc⟩ := exists_pointwiseColimitCone p hp
  exact ⟨c, isColimitCone_of_pointwise c hc⟩

/-- 概要：同じ図式上の同型な余錐の間で点ごとの余極限性は保たれる。
方針：余錐の同型を各評価の後合成で写す。
規約：同型は図式の下の coslice で取る。使われ方：関手圏の余極限性からの逆向き。 -/
lemma IsPointwiseColimitCone.of_vertexIso {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (hc : IsPointwiseColimitCone c) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) c d) :
    IsPointwiseColimitCone d := by
  intro k
  exact (hc k).of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)))

/-- 概要：各点で余極限が存在するとき、関手圏の任意の余極限余錐も各点で余極限。
方針：点ごとに普遍な自然な余錐を別に構成し、余極限の一意性で比較する。
規約：点ごとの存在前提を省略しない。使われ方：構成済みの族を各点で評価する向き。 -/
lemma isPointwiseColimitCone_of_isColimitCone_of_hasPointwiseColimits {J K X : SSet.{u}}
    [Quasicategory X] {p : J ⟶ (ihom K).obj X} (hp : HasPointwiseColimits p)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) : IsPointwiseColimitCone c := by
  obtain ⟨d, hd⟩ := exists_pointwiseColimitCone p hp
  exact hd.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso d c (isColimitCone_of_pointwise d hd) hc)

/-- 概要：各点で余極限が存在すれば、自然な余錐の関手圏での余極限性と点ごとの余極限性は同値。
方針：点ごとの存在・一意性による向きと、点ごとの判定による向きを合わせる。
規約：X は quasicategory、J・K は任意。使われ方：HTT 5.1.2.2 の余極限の完全な比較。 -/
@[kerodon 05QG]
lemma isColimitCone_iff_pointwise_of_hasPointwiseColimits {J K X : SSet.{u}}
    [Quasicategory X] {p : J ⟶ (ihom K).obj X} (hp : HasPointwiseColimits p)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ IsPointwiseColimitCone c :=
  ⟨isPointwiseColimitCone_of_isColimitCone_of_hasPointwiseColimits hp c,
    isColimitCone_of_pointwise c⟩

/-- 概要：評価した span が全て余極限を持てば、関手圏の正方形の押し出し性は点ごとの押し出し性と同値。
方針：正方形を span の余錐に直し、点ごとの余極限の比較を使う。
規約：存在前提を明記する。使われ方：cofiber の族の普遍性を評価へ戻す。 -/
lemma isPushoutSquare_iff_pointwise_of_hasPointwiseColimits {K X : SSet.{u}}
    [Quasicategory X] (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom K).obj X)
    (hp : HasPointwiseColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F ↔ ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) :=
  isColimitCone_iff_pointwise_of_hasPointwiseColimits hp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
