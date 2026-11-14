module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.BarrattEccles.Modules.TotalLocalization
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerAnodyneReplacement

/-!
# 同じ BE 全加群の射影の inner fibration への置換

概要：HTT Theorem 2.0.0.6 の内ホーン分解を同じ全加群の射影に適用する。
方針：元の射影を inner anodyne な包含と inner fibration に分解する。
規約：同じ CAlg を底に保つ。fiber の同定と一般の Cartesian lift は別に検証する。
使われ方：M10 の実全族の射影と元の指定弱 lift の移送。
Kerodon Theorem 5.2.4.1（Tag 024N）の同じ内ホーン置換を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MorphismProperty
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
variable (A : Type u) [CommRing A]

/-- 概要：同じ射影の内ホーン分解のデータ（HTT Theorem 2.0.0.6）。
方針：既存の小対象論法の指定分解を一度だけ選ぶ。
規約：外部から分解を仮定しない。使われ方：同じ全圏・包含・射影の定義。 -/
def moduleTotalInnerFactorization :
    MapFactorizationData innerHornInclusions.rlp.llp innerHornInclusions.rlp
      (moduleTotalProjection A) :=
  factorizationData innerHornInclusions.rlp.llp innerHornInclusions.rlp (moduleTotalProjection A)

/-- 概要：同じ BE 全加群の射影を内ホーンで置換した全空間（HTT Theorem 2.0.0.6）。
方針：元の射影の分解の中間対象を取る。
規約：元の全圏と同値。使われ方：実全族の射影の始域。 -/
def moduleTotalInnerInfinity : SSet.{u+1} := (moduleTotalInnerFactorization A).Z

/-- 概要：元の全加群局所化から同じ置換への包含（HTT Theorem 2.0.0.6）。
方針：指定分解の左因子を取る。
規約：全単体の実写像。使われ方：元の指定辺と全関手の移送。 -/
def moduleTotalInnerInclusion : moduleTotalInfinity A ⟶ moduleTotalInnerInfinity A :=
  (moduleTotalInnerFactorization A).i

/-- 概要：同じ CAlg 上の置換後の全加群射影（HTT Theorem 2.0.0.6）。
方針：指定分解の右因子を取る。
規約：底を変えない。使われ方：native な相対ホーン条件の射影。 -/
def moduleTotalInnerProjection : moduleTotalInnerInfinity A ⟶ CAlg_R A :=
  (moduleTotalInnerFactorization A).p

/-- 概要：同じ置換後の射影は inner fibration（HTT Theorem 2.0.0.6）。
方針：内ホーン分解の右因子の条件を使う。
規約：任意次数の内ホーン。使われ方：元の弱 lift の native な Cartesian 性。 -/
instance moduleTotalInnerProjection_innerFibration : InnerFibration (moduleTotalInnerProjection A) :=
  ⟨(moduleTotalInnerFactorization A).hp⟩

/-- 概要：同じ置換後の全加群空間は準圏（HTT Theorem 2.0.0.6）。
方針：同じ CAlg 上の inner fibration の始域の充填性を使う。
規約：モデル圏の仮定を加えない。使われ方：全加群族の native な全空間。 -/
instance moduleTotalInnerInfinity_quasicategory : Quasicategory (moduleTotalInnerInfinity A) :=
  quasicategory_of_innerFibration (moduleTotalInnerProjection A)

/-- 概要：同じ全加群の包含は inner anodyne（HTT Theorem 2.0.0.6）。
方針：元の分解の左因子の条件を使う。
規約：指定された実包含。使われ方：全圏の同値と図式の移送。 -/
lemma moduleTotalInnerInclusion_innerAnodyne : innerAnodyneExtensions (moduleTotalInnerInclusion A) :=
  (moduleTotalInnerFactorization A).hi

/-- 概要：包含後の射影は元の同じ全射影（HTT Theorem 2.0.0.6）。
方針：指定分解の厳密な合成式を使う。
規約：全単体の等式。使われ方：元の底の指定辺の保存。 -/
lemma moduleTotalInnerInclusion_projection :
    moduleTotalInnerInclusion A ≫ moduleTotalInnerProjection A = moduleTotalProjection A :=
  (moduleTotalInnerFactorization A).fac

/-- 概要：元の全圏の包含は同じ準圏の同値（HTT Theorem 2.0.0.6）。
方針：内アノディン性による全関手圏の前合成同値を使う。
規約：元の包含自体の同値性。使われ方：同じ台・単位・全比較の移送。 -/
lemma moduleTotalInnerInclusion_isQCatEquivalence : IsQCatEquivalence (moduleTotalInnerInclusion A) :=
  (isPrecompositionEquivalence_of_innerAnodyne _
    (moduleTotalInnerInclusion_innerAnodyne A)).isQCatEquivalence

attribute [cite HTT "2.0.0.6" (partial := component)
  "既存の内ホーン因子分解を同じ BE 全加群射影へ適用する部分。一般の lift の存在は含まない。"]
  moduleTotalInnerFactorization moduleTotalInnerInfinity moduleTotalInnerInclusion
  moduleTotalInnerProjection moduleTotalInnerProjection_innerFibration
  moduleTotalInnerInfinity_quasicategory moduleTotalInnerInclusion_innerAnodyne
  moduleTotalInnerInclusion_projection moduleTotalInnerInclusion_isQCatEquivalence

end SerrePositivity.EInfinity.BarrattEccles
