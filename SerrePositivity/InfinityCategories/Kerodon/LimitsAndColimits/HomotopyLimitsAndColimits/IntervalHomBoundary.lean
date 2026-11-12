module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.KanEquivalencePaths
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedInterval
public import SerrePositivity.Spectra.Pointed.SmashMonoidal
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
概要：通常の区間からの内部 Hom の両端点の同時評価は Kan fibration。
方針：二端点の余積からの内部 Hom の積表示と、単射への制限の fibration 性を使う。
規約：標的の Kan 性だけを使い、端点の第一成分を終点一、第二成分を始点零とする。
使われ方：Goerss–Jardine I §7、Kerodon 7.5.4.6（Tag 03BB）、元の比較射の導来 fiber。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section

/-- 概要：定値頂点への制限と単位の内部 Hom の評価の合成は通常の頂点評価。
方針：内部 Hom の各単体に恒等写像と定値単体を代入する。
規約：始域と標的に Kan 性は要求しない。
使われ方：余積の両成分を区間の端点評価に同定する。 -/
lemma homPre_const_unitIsoSelf {K Y : SSet.{u}} (v : K _⦋0⦌) :
    (MonoidalClosed.pre (SSet.const (X := 𝟙_ SSet.{u}) v)).app Y ≫
      (unitIsoSelf (X := Y)).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v := by
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro F
  rfl

/-- 概要：二つの単位の余積からの内部 Hom は単位からの内部 Hom の積。
方針：反変内部 Hom の極限保存を余積の反対に適用する。
規約：第一射影は余積の第一成分への制限。
使われ方：二端点からの内部 Hom の積表示。 -/
def intervalHomBoundaryIsLimit (Y : SSet.{u}) :
    IsLimit (BinaryFan.mk
      ((MonoidalClosed.pre (coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))).app Y)
      ((MonoidalClosed.pre (coprod.inr : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))).app Y)) := by
  have h := mapIsLimitOfPreservesOfIsLimit (MonoidalClosed.internalHom.flip.obj Y) _ _
    (BinaryCofan.IsColimit.op (coprodIsCoprod (𝟙_ SSet.{u}) (𝟙_ SSet.{u})))
  exact h

/-- 概要：二端点からの内部 Hom は二つの標的への評価を射影とする積。
方針：単位からの内部 Hom の標準同型を両射影へ合成する。
規約：通常の単体集合の積の普遍性。
使われ方：両端点の積表示の同型と成分計算。 -/
def intervalHomBoundaryEvaluationIsLimit (Y : SSet.{u}) :
    IsLimit (BinaryFan.mk
      ((MonoidalClosed.pre (coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))).app Y ≫
        (unitIsoSelf (X := Y)).hom)
      ((MonoidalClosed.pre (coprod.inr : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))).app Y ≫
        (unitIsoSelf (X := Y)).hom)) :=
  BinaryFan.isLimitCompRightIso _ (unitIsoSelf (X := Y)).hom
    (BinaryFan.isLimitCompLeftIso _ (unitIsoSelf (X := Y)).hom (intervalHomBoundaryIsLimit Y))

/-- 概要：二端点からの内部 Hom と標的二つの積との標準同型。
方針：二つの単位の内部 Hom の評価同型を積の射影へ合成して普遍性を比較する。
規約：第一成分が終点、第二成分が始点。
使われ方：区間の境界への制限の fibration を両端点評価へ移す。 -/
def intervalHomBoundaryEvaluationIso (Y : SSet.{u}) :
    (ihom ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))).obj Y ≅ Y ⨯ Y :=
  (intervalHomBoundaryEvaluationIsLimit Y).conePointUniqueUpToIso
    (t := BinaryFan.mk (prod.fst : Y ⨯ Y ⟶ Y) prod.snd) (prodIsProd Y Y)

/-- 概要：境界の内部 Hom の積表示の第一射影は第一成分の評価。
方針：極限の一意同型の射影の計算を使う。
規約：区間の端点では終点一に対応する。
使われ方：両端点評価の第一成分の計算。 -/
lemma intervalHomBoundaryEvaluationIso_hom_fst (Y : SSet.{u}) :
    (intervalHomBoundaryEvaluationIso Y).hom ≫ prod.fst =
      (MonoidalClosed.pre (coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))).app Y ≫
        (unitIsoSelf (X := Y)).hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp (intervalHomBoundaryEvaluationIsLimit Y)
    (prodIsProd Y Y) ⟨WalkingPair.left⟩

/-- 概要：境界の内部 Hom の積表示の第二射影は第二成分の評価。
方針：極限の一意同型の射影の計算を使う。
規約：区間の端点では始点零に対応する。
使われ方：両端点評価の第二成分の計算。 -/
lemma intervalHomBoundaryEvaluationIso_hom_snd (Y : SSet.{u}) :
    (intervalHomBoundaryEvaluationIso Y).hom ≫ prod.snd =
      (MonoidalClosed.pre (coprod.inr : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))).app Y ≫
        (unitIsoSelf (X := Y)).hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp (intervalHomBoundaryEvaluationIsLimit Y)
    (prodIsProd Y Y) ⟨WalkingPair.right⟩

/-- 概要：通常の区間からの内部 Hom の両端点の同時評価。
方針：二端点への制限を内部 Hom の積表示へ合成する。
規約：第一成分は頂点一、第二成分は頂点零。
使われ方：任意の Kan 複体間の比較射の path 置換のホーン充填。 -/
def intervalHomEndpoints (Y : SSet.{u}) : (ihom (Δ[1] : SSet.{u})).obj Y ⟶ Y ⨯ Y :=
  (MonoidalClosed.pre _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right).app Y ≫ (intervalHomBoundaryEvaluationIso Y).hom

/-- 概要：Kan 複体を標的とする両端点評価は Kan fibration。
方針：単射な二端点包含への内部 Hom の制限と同型を合成する。
規約：比較射の fibration 性は使わない。
使われ方：path 置換の終点射を fibration にする。 -/
instance intervalHomEndpoints_fibration (Y : SSet.{u}) [KanComplex Y] :
    Fibration (intervalHomEndpoints Y) := by
  unfold intervalHomEndpoints
  infer_instance

/-- 概要：両端点評価の第一射影は区間の終点一での評価。
方針：前合成の関手性と余積の第一成分の計算を使う。
規約：元の evaluateFunctorAt と厳密に一致する。
使われ方：path 置換の終点を指定する。 -/
lemma intervalHomEndpoints_fst (Y : SSet.{u}) :
    intervalHomEndpoints Y ≫ prod.fst = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) := by
  rw [intervalHomEndpoints, Category.assoc, intervalHomBoundaryEvaluationIso_hom_fst,
    ← Category.assoc, ← NatTrans.comp_app, ← MonoidalClosed.pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inl]
  exact homPre_const_unitIsoSelf _

/-- 概要：両端点評価の第二射影は区間の始点零での評価。
方針：前合成の関手性と余積の第二成分の計算を使う。
規約：元の evaluateFunctorAt と厳密に一致する。
使われ方：path 置換の元の始域との整合条件。 -/
lemma intervalHomEndpoints_snd (Y : SSet.{u}) :
    intervalHomEndpoints Y ≫ prod.snd = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) := by
  rw [intervalHomEndpoints, Category.assoc, intervalHomBoundaryEvaluationIso_hom_snd,
    ← Category.assoc, ← NatTrans.comp_app, ← MonoidalClosed.pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_inr]
  exact homPre_const_unitIsoSelf _

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
