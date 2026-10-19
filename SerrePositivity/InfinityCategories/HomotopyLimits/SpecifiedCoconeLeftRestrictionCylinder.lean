module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftHomTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialEvaluationHomotopyTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitHomEnd
public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyTriangleClasses

/-!
概要：共通 end の左 HL と、実際の標準左輸送三角形の全 Hom 族を同じ評価上で比較する。
方針：厳密な引き戻しの制限式で始点を揃え、元の二円柱を二辺として三角形を充填する。
規約：HL の raw な円柱と元の左二単体の族を保持し、終点評価を全時刻で固定する。
使われ方：左側の Hom 係数を native な共通脚と指定輸送経路へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (hB : IsColimitCone dB) (dC : JoinCocone (j ≫ p))
  (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "V" => specifiedCoconeCommonHomFamily hp p c hc dB dC y
local notation "W" => coconePointHomFamily (partialColimitSpecifiedPathCocone hp p c hc dB dC) y
local notation "U" => W ≫ cosliceRestrictionFiberMap p i y
local notation "r" => normalizedCoconeRestrictionFiber (i ≫ p) f rfl y
local notation "DL" => colimitAttachmentRestrictionCylinderData c hc f (i ≫ p) rfl dB hB y
local notation "P" => leftFibrationInitialProjection q c y ≫
  Iso.hom (leftFibrationInitialBaseIso q c y)

/-- 正規化した左境界への制限も、元の同じ共通族に厳密に一致する。 -/
lemma specifiedCoconeLeftHomRestriction_common : U ≫ r = V := by
  have hr : r = cosliceRestrictionFiberMap (i ≫ p) f y := by
    simp only [normalizedCoconeRestrictionFiber_eq, eqToHom_refl, Category.comp_id]
  exact (congrArg (fun z ↦ U ≫ z) hr).trans
    ((Category.assoc _ _ _).trans (specifiedCoconeLeftCommonHomFamily_eq hp p c hc dB dC y))

/-- 元の左制限の中間持ち上げを、指定余錐の全 Hom の左制限で読む。 -/
def specifiedCoconeLeftRestrictionInitialHomFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      leftFibrationInitialTotal q c y := U ≫ (DL).lift

/-- 左 HL の同じ評価固定中間円柱を、元の全 Hom 上で表示する。 -/
def specifiedCoconeLeftRestrictionInitialHomCylinder : SSet.Homotopy
    (V ≫ leftFibrationInitialSection q c hc y)
    (specifiedCoconeLeftRestrictionInitialHomFamily hp p c hc dB hB dC y) := by
  let H := functorHomotopyPrecomp (DL).homotopy U
  exact
    { h := H.h
      h₀ := by
        change SSet.ι₀ ≫ H.h = V ≫ leftFibrationInitialSection q c hc y
        calc
          _ = U ≫ (r ≫ leftFibrationInitialSection q c hc y) := by
            simpa only [initialRestrictionEdgeFamily_vertexFiberLift,
              normalizedCoconeRestrictionFiber, Category.assoc] using H.h₀
          _ = (U ≫ r) ≫ leftFibrationInitialSection q c hc y := (Category.assoc _ _ _).symm
          _ = _ := congrArg (fun z ↦ z ≫ leftFibrationInitialSection q c hc y)
            (specifiedCoconeLeftHomRestriction_common hp p c hc dB dC y)
      h₁ := by
        change SSet.ι₁ ≫ H.h = specifiedCoconeLeftRestrictionInitialHomFamily hp p c hc dB hB dC y
        exact H.h₁
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro z
        exact False.elim z.1.property }

/-- 同じ円柱の評価は、元の共通族を全時刻で固定する。 -/
lemma specifiedCoconeLeftRestrictionInitialHomCylinder_evaluation :
    (specifiedCoconeLeftRestrictionInitialHomCylinder hp p c hc dB hB dC y).h ≫
        leftFibrationInitialEvaluation q c y = fst _ (Δ[1] : SSet.{u + 1}) ≫ V := by
  change ((U ▷ (Δ[1] : SSet.{u + 1})) ≫ (DL).homotopy.h) ≫
    leftFibrationInitialEvaluation q c y = _
  calc
    _ = (U ▷ (Δ[1] : SSet.{u + 1})) ≫
        ((DL).homotopy.h ≫ leftFibrationInitialEvaluation q c y) := Category.assoc _ _ _
    _ = (U ▷ (Δ[1] : SSet.{u + 1})) ≫ (fst _ Δ[1] ≫ r) :=
      congrArg (fun z ↦ (U ▷ (Δ[1] : SSet.{u + 1})) ≫ z)
        (colimitAttachmentRestrictionCylinderData_evaluation c hc f (i ≫ p) rfl dB hB y)
    _ = ((U ▷ (Δ[1] : SSet.{u + 1})) ≫ fst _ Δ[1]) ≫ r := (Category.assoc _ _ _).symm
    _ = (fst _ Δ[1] ≫ U) ≫ r := congrArg (fun z ↦ z ≫ r) (whiskerRight_fst U Δ[1])
    _ = fst _ Δ[1] ≫ V := (Category.assoc _ _ _).trans
      (congrArg (fun z ↦ fst _ Δ[1] ≫ z)
        (specifiedCoconeLeftHomRestriction_common hp p c hc dB dC y))

/-- 元の左二単体全体の中間族を比較する、同じ共通族の評価を固定した円柱データ。 -/
def specifiedCoconeLeftHomCylinderData : InitialEvaluationCylinder q c y V hc
    (specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y) :=
  initialEvaluationCylinder q c y V hc _
    (specifiedCoconeLeftInitialHomFamily_evaluation hp p c hc dB dC y)

/-- 左 HL と実際の左二単体の円柱を二辺として保つ、評価固定の同じ三角形。 -/
def specifiedCoconeLeftRestrictionTriangle : InitialEvaluationHomotopyTriangle q c y V
    (specifiedCoconeLeftRestrictionInitialHomCylinder hp p c hc dB hB dC y)
    (specifiedCoconeLeftHomCylinderData hp p c hc dB dC y).homotopy :=
  initialEvaluationHomotopyTriangle q c y V _ _ hc
    (specifiedCoconeLeftRestrictionInitialHomCylinder_evaluation hp p c hc dB hB dC y)
    (specifiedCoconeLeftHomCylinderData hp p c hc dB dC y).evaluation
local notation "T" => specifiedCoconeLeftRestrictionTriangle hp p c hc dB hB dC y

/-- 同じ三角形の第三辺による、左制限の中間族と元の左三角形の中間族の比較。 -/
def specifiedCoconeLeftRestrictionHomotopy : SSet.Homotopy
    (specifiedCoconeLeftRestrictionInitialHomFamily hp p c hc dB hB dC y)
    (specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y) :=
  initialEvaluationHomotopyTriangleThird q c y V _ _ T

/-- 第三辺も、同じ元の共通族の評価を全時刻で保つ。 -/
lemma specifiedCoconeLeftRestrictionHomotopy_evaluation :
    (specifiedCoconeLeftRestrictionHomotopy hp p c hc dB hB dC y).h ≫
        leftFibrationInitialEvaluation q c y = fst _ (Δ[1] : SSet.{u + 1}) ≫ V :=
  initialEvaluationHomotopyTriangleThird_evaluation _ _ _ _ _ _ _

/-- 正規化した左 HL を、同じ中間円柱の射影として保持する。 -/
def specifiedCoconeLeftProjectedCylinder : SSet.Homotopy
    (V ≫ coconeMappingSpaceHomComparison c hc y)
    (specifiedCoconeLeftRestrictionInitialHomFamily hp p c hc dB hB dC y ≫ P) :=
  functorHomotopyPostcomp
    (specifiedCoconeLeftRestrictionInitialHomCylinder hp p c hc dB hB dC y) P

/-- 左 Hom への射影は、元の HL に全 Hom の左制限を前合成した円柱そのもの。 -/
lemma specifiedCoconeLeftProjectedCylinder_raw :
    (specifiedCoconeLeftProjectedCylinder hp p c hc dB hB dC y).h =
      (functorHomotopyPrecomp (partialColimitHomEndLeftCylinder p y c hc dB hB) U).h :=
  Category.assoc _ _ _

/-- 元の左三角形の中間族の Hom 比較を、同じ評価固定円柱から得る。 -/
def specifiedCoconeLeftHomCylinderComparison : SSet.Homotopy
    (V ≫ coconeMappingSpaceHomComparison c hc y)
    (specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y ≫ P) :=
  functorHomotopyPostcomp (specifiedCoconeLeftHomCylinderData hp p c hc dB dC y).homotopy P

/-- 同じ第三辺を左 Hom へ射影した、元の両中間族の比較。 -/
def specifiedCoconeLeftRestrictionHomComparison : SSet.Homotopy
    (specifiedCoconeLeftRestrictionInitialHomFamily hp p c hc dB hB dC y ≫ P)
    (specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y ≫ P) :=
  functorHomotopyPostcomp (specifiedCoconeLeftRestrictionHomotopy hp p c hc dB hB dC y) P

/-- 左 HL、同じ第三辺、元の左三角形の比較円柱の類は、実際の三角形に従って合成する。 -/
lemma specifiedCoconeLeftRestrictionTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeLeftProjectedCylinder hp p c hc dB hB dC y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeLeftRestrictionHomComparison hp p c hc dB hB dC y)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeLeftHomCylinderComparison hp p c hc dB dC y)) := by
  apply homotopyTriangle_homMk_comp _ _ _ ((T).family ≫ P)
  · exact (Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ P) (T).first)
  · exact (Category.assoc _ _ _).symm
  · exact (Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ P) (T).diagonal)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
