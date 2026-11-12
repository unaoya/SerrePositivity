module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingNullSquare

/-!
概要：恒等 Hom gluing の実 cone が可縮な対象の充満 dg 圏を保持する。
方針：対象別の実収縮を性質とし、元関手を全 Hom ごと厳密に因子化する。
規約：全関手の自然収縮や、対角との S 内同型を要求しない。
使われ方：元共有対角を保つ上合成二単体と実零化面の構成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [DGCategory R C] [Small.{u} C]
local notation "L" => DGIdentityHomGluing R C
local notation "D" => DGIdentityHomGluingDifference R C
local notation "δ" => dgIdentityHomGluingDifference R C

/-- 概要：元実 cone の対象別収縮を指定する性質。
方針：同じ cone 小模型の Hom 内の境界を使う。
規約：核方向の自然性は含めない。使われ方：実零化始域の対象条件。 -/
def dgIdentityHomGluingNullProperty (x : L) : Prop :=
  ∃ h : GradedHom R ((δ).obj x) ((δ).obj x) (-1),
    (homObject R (D) ((δ).obj x) ((δ).obj x)).d (-1) 0 h =
      (unitElement R ((δ).obj x)).val

/-- 概要：元 cone が可縮な実 gluing 対象の充満 dg 圏 V。
方針：対象だけを制限し全 Hom を保持する。
規約：元小基底と元比較射を保持。使われ方：厳密因子化の中間対象。 -/
abbrev DGIdentityHomGluingNullDomain :=
  DGFullSubcategory (L) (dgIdentityHomGluingNullProperty R C)
local notation "V" => DGIdentityHomGluingNullDomain R C

instance dgIdentityHomGluingNullDomainEnrichment : DGCategory R (V) :=
  dgFullSubcategoryEnrichment R (L) (dgIdentityHomGluingNullProperty R C)

instance dgIdentityHomGluingNullDomainSmall : Small.{u} (V) := by
  change Small.{u} {x : (L) // dgIdentityHomGluingNullProperty R C x}
  infer_instance

/-- 概要：V から元 gluing への全 Hom を保つ包含。
方針：同じ充満包含を使用。
規約：対象を選び直さない。使われ方：元共有対角の終端。 -/
def dgIdentityHomGluingNullInclusion : DGFunctor R (V) (L) :=
  dgFullSubcategoryInclusion R (L) (dgIdentityHomGluingNullProperty R C)

/-- 概要：V を固定 S の実対象にする。
方針：元小対象集合を共通宇宙へ持ち上げる。
規約：全 Perf の Small 性を仮定しない。使われ方：上合成三角形の中間頂点。 -/
def dgIdentityHomGluingNullInput : PerfDGInput.{u, u + 1} R :=
  dgKUniverseInput.{u, u + 1, u + 1} R (V)

/-- 概要：同じ V 包含を固定 S の実辺にする。
方針：元包含の全 Hom を宇宙持ち上げする。
規約：元包含を保持。使われ方：上合成三角形の第二短辺。 -/
def dgIdentityHomGluingNullInputMap :
    dgIdentityHomGluingNullInput R C ⟶ dgIdentityHomGluingGluingInput R C :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1}
    (dgIdentityHomGluingNullInclusion R C))

variable {P : Type (u + 1)} [DGCategory R P]

/-- 概要：元関手を同じ cone 可縮対象の充満圏へ厳密因子化する。
方針：元の対象と全 Hom をそのまま使用。
規約：対象別収縮の自然性は不要。使われ方：元対角を保持する第一短辺。 -/
def dgIdentityHomGluingNullFactor (F : DGFunctor R P (L))
    (hF : ∀ x, dgIdentityHomGluingNullProperty R C (F.obj x)) : DGFunctor R P (V) where
  obj x := ⟨F.obj x, hF x⟩
  map := F.map
  map_id := F.map_id
  map_comp := F.map_comp

/-- 概要：充満圏への因子化は元関手を厳密回収する。
方針：元全 Hom 上の恒等合成を消去する。
規約：自然同型でなく関手等号。使われ方：元共有対角の回収。 -/
lemma dgIdentityHomGluingNullFactor_inclusion (F : DGFunctor R P (L))
    (hF : ∀ x, dgIdentityHomGluingNullProperty R C (F.obj x)) :
    (dgIdentityHomGluingNullFactor R C F hF).comp
      (dgIdentityHomGluingNullInclusion R C) = F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  change F.map x y ≫ 𝟙 _ = _
  exact Category.comp_id _

variable [Small.{u} P]

/-- 概要：同じ厳密因子化の第一短辺を固定 S に置く。
方針：元全 Hom を宇宙持ち上げする。
規約：元始域を保持。使われ方：元共有対角の上三角。 -/
def dgIdentityHomGluingNullFactorInputMap (F : DGFunctor R P (L))
    (hF : ∀ x, dgIdentityHomGluingNullProperty R C (F.obj x)) :
    dgKUniverseInput.{u, u + 1, u + 1} R P ⟶ dgIdentityHomGluingNullInput R C :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1}
    (dgIdentityHomGluingNullFactor R C F hF))

/-- 概要：固定 S でも元の厳密合成辺を回収する。
方針：宇宙持ち上げの合成保存と元の因子化等号を使用。
規約：元辺の等号。使われ方：K-S2 との共有対角を維持する。 -/
lemma dgIdentityHomGluingNullFactorInputMap_comp (F : DGFunctor R P (L))
    (hF : ∀ x, dgIdentityHomGluingNullProperty R C (F.obj x)) :
    dgIdentityHomGluingNullFactorInputMap R C F hF ≫ dgIdentityHomGluingNullInputMap R C =
      ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1} F) := by
  apply ULift.down_injective
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor_comp _ _).symm.trans
    (congrArg (fun T => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1} T)
      (dgIdentityHomGluingNullFactor_inclusion R C F hF))

/-- 概要：元の厳密合成辺を対角として保つ実 S 上二単体。
方針：厳密因子化の合成二単体を同じ対角等号で移す。
規約：ν 像だけの三角形ではない。使われ方：共有対角を保つ比較面。 -/
def dgIdentityHomGluingNullFactorTriangle (F : DGFunctor R P (L))
    (hF : ∀ x, dgIdentityHomGluingNullProperty R C (F.obj x)) : SSet.Edge.CompStruct
    (X := dgKInputInfinity.{u, u + 1} R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgIdentityHomGluingNullFactorInputMap R C F hF))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgIdentityHomGluingNullInputMap R C))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1} F))) := by
  have t : SSet.Edge.CompStruct (X := dgKInputInfinity.{u, u + 1} R)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgIdentityHomGluingNullFactorInputMap R C F hF))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgIdentityHomGluingNullInputMap R C))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgIdentityHomGluingNullFactorInputMap R C F hF ≫
        dgIdentityHomGluingNullInputMap R C)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct _ _
  exact t.ofEq rfl rfl (by congr 1)

/-- 概要：元の二関手の厳密合成辺を対角に保つ V 因子化の上二単体。
方針：抽象的な二関手の段階で宇宙持ち上げの合成保存を照合する。
規約：具体的巨大模型の正規化に依存しない。使われ方：元厚核包含と実中央辺の特殊化。 -/
def dgIdentityHomGluingNullFactorCompositeTriangle
    (T : Type (u + 1)) [DGCategory R T] [Small.{u} T]
    (k : DGFunctor R P T) (F : DGFunctor R T (L))
    (hF : ∀ x, dgIdentityHomGluingNullProperty R C (F.obj (k.obj x))) :
    SSet.Edge.CompStruct (X := dgKInputInfinity.{u, u + 1} R)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgIdentityHomGluingNullFactorInputMap R C (k.comp F) hF))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgIdentityHomGluingNullInputMap R C))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        ((ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1} k) :
          dgKUniverseInput.{u, u + 1, u + 1} R P ⟶ dgKUniverseInput.{u, u + 1, u + 1} R T) ≫
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1} F) :
            dgKUniverseInput.{u, u + 1, u + 1} R T ⟶ dgIdentityHomGluingGluingInput R C))) := by
  have t := dgIdentityHomGluingNullFactorTriangle R C (k.comp F) hF
  exact t.ofEq rfl rfl (by
    congr 1 <;> apply ULift.down_injective <;> exact dgUniverseLiftFunctor_comp k F)

/-- 概要：V の同じ実 cone 合成に対象別収縮を指定する。
方針：対象条件の証拠を全対象商の延長入力に渡す。
規約：収縮の自然性を仮定しない。使われ方：V の実零化面。 -/
def dgIdentityHomGluingNullContracted : DGQuotient.ContractedFunctor R
    (dgIdentityHomGluingNullInput R C) Set.univ
    (dgIdentityHomGluingDifferenceInput R C) where
  toDGFunctor := (dgIdentityHomGluingNullInputMap R C).down.comp
    (dgIdentityHomGluingDifferenceInputMap R C).down
  homotopy x := x.val.label.down.property.choose
  d_homotopy x := x.val.label.down.property.choose_spec

/-- 概要：V の包含・元実 cone 差を保持する固定 S 零化面。
方針：Sp 正本の指定収縮からの構成を適用する。
規約：元の四辺全体を保持。使われ方：共通長方形の新しい実右面。 -/
def dgIdentityHomGluingNullDomainSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R :=
  (exists_dgFixedNullSquare R (dgIdentityHomGluingNullInputMap R C)
    (dgIdentityHomGluingDifferenceInputMap R C)
    (dgIdentityHomGluingNullContracted R C) rfl).choose

/-- 概要：V の零化面の元四辺を回収する。
方針：同じ Sp 正本の構成の仕様を取り出す。
規約：包含・差・商二辺の厳密等号。使われ方：全指定境界での貼合せ。 -/
lemma dgIdentityHomGluingNullDomainSquare_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgIdentityHomGluingNullDomainSquare R C = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgIdentityHomGluingNullInputMap R C)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgIdentityHomGluingNullDomainSquare R C = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgIdentityHomGluingDifferenceInputMap R C)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgIdentityHomGluingNullDomainSquare R C = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := dgIdentityHomGluingNullInput R C))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgIdentityHomGluingNullDomainSquare R C = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullTop R (dgIdentityHomGluingNullContracted R C))).edge :=
  (exists_dgFixedNullSquare R (dgIdentityHomGluingNullInputMap R C)
    (dgIdentityHomGluingDifferenceInputMap R C)
    (dgIdentityHomGluingNullContracted R C) rfl).choose_spec

/-- 概要：元恒等対角は V へ厳密に因子化する。
方針：同じ恒等 cone の指定収縮をそのまま用いる。
規約：V と対角始域の同値性は別証明。使われ方：ν 面比較の元対角側。 -/
def dgIdentityHomGluingDiagonalNullFactor : DGFunctor R C (V) :=
  dgIdentityHomGluingNullFactor R C (dgIdentityHomGluingDiagonal R C)
    (fun x => ⟨dgIdentityHomGluingContractingElement R C x,
      dgIdentityHomGluingContractingElement_d R C x⟩)

/-- 概要：V への元対角因子化は元対角を厳密回収する。
方針：元の厳密因子化等号を適用。
規約：同型類で代用しない。使われ方：元対角境界の照合。 -/
lemma dgIdentityHomGluingDiagonalNullFactor_inclusion :
    (dgIdentityHomGluingDiagonalNullFactor R C).comp
      (dgIdentityHomGluingNullInclusion R C) = dgIdentityHomGluingDiagonal R C :=
  dgIdentityHomGluingNullFactor_inclusion R C _ _

end SerrePositivity.KST.SConstruction
