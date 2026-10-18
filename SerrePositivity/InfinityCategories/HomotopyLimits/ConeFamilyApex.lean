module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeRepresentableCriterion
public import SerrePositivity.InfinityCategories.Core.SliceConeFamilyEquivalence

/-!
概要：内部 Hom の錐の模型から頂点への射影と、slice の頂点 fiber からの比較。
方針：錐の左包含への制限を一点で評価し、既存の slice の比較の頂点との可換性を示す。
規約：内部 Hom の固定図式は全ての次数で p に固定する。
使われ方：Kerodon 4.6.6.8、7.4.1.6、7.5.4.6 の錐の頂点 fiber と切断模型の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：内部 Hom で表す錐をその頂点で評価する射影。
方針：左の一点への制限の後で一点の関手空間の評価を使う。
規約：元の標的 X の quasicategory 性は要求しない。
使われ方：Kerodon 4.6.6.8、7.4.1.6 の固定頂点の共通模型。 -/
def coneFamilyApex {K X : SSet.{u}} (p : K ⟶ X) : coneFamily p ⟶ X :=
  vertexFiberι (coneRestriction K X) (functorVertex p) ≫
    (pre (joinInl (Δ[0] : SSet.{u}) K)).app X ≫ (pointFunctorEvaluationIso X).hom

/-- 概要：slice から内部 Hom の錐への標準比較は錐の頂点を保つ。
方針：左の一点への制限で直積と join の比較を計算する。
規約：全ての次数における射の厳密な等式。
使われ方：Kerodon 4.6.6.8、7.4.1.6 の頂点 fiber の比較射の構成。 -/
lemma sliceConeFamilyMap_apex {K X : SSet.{u}} (p : K ⟶ X) :
    sliceConeFamilyMap p ≫ coneFamilyApex p = sliceOverProjection p := by
  let S := sliceOver p
  have hswap : (joinInl (Δ[0] : SSet.{u}) K ▷ S) ≫
      (β_ (join (Δ[0] : SSet.{u}) K) S).hom =
      (β_ (Δ[0] : SSet.{u}) S).hom ≫ (S ◁ joinInl Δ[0] K) := rfl
  have hleft : (joinInl (Δ[0] : SSet.{u}) K ▷ S) ≫
      sliceConeFamilyUncurry p = snd (Δ[0] : SSet.{u}) S ≫ sliceOverProjection p := by
    change (joinInl (Δ[0] : SSet.{u}) K ▷ S) ≫
      (β_ (join (Δ[0] : SSet.{u}) K) S).hom ≫ joinTensorLeft S Δ[0] K ≫
      joinMap (fst S Δ[0]) (𝟙 K) ≫ sliceOverUncurry (𝟙 S) = _
    rw [← Category.assoc (joinInl (Δ[0] : SSet.{u}) K ▷ S), hswap]
    simp only [Category.assoc]
    rw [← Category.assoc (S ◁ joinInl (Δ[0] : SSet.{u}) K), joinTensorLeft_inl]
    rw [← Category.assoc (joinInl (S ⊗ Δ[0]) K), joinInl_joinMap]
    simp only [Category.assoc]
    rw [sliceOverUncurry_projection, Category.id_comp]
    rfl
  change (sliceConeFamilyMap p ≫
    vertexFiberι (coneRestriction K X) (functorVertex p)) ≫
    (pre (joinInl (Δ[0] : SSet.{u}) K)).app X ≫
    (pointFunctorEvaluationIso X).hom = _
  rw [sliceConeFamilyMap, vertexFiberLift_ι, ← Category.assoc, curry_pre_app, hleft]
  change curry (snd (Δ[0] : SSet.{u}) S ≫ sliceOverProjection p) ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = _
  rw [curry_evaluateFunctorAt_vertex, ← Category.assoc, lift_snd]
  exact Category.id_comp _

/-- 概要：内部 Hom の錐の模型の頂点 x 上の厳密な fiber。
方針：頂点評価の fiber を取る。
規約：通常の slice の頂点 fiber と、同値性を証明する前に同一視しない。
使われ方：Kerodon 4.6.6.8、7.4.1.6、7.5.4.6 の二つの錐の模型の共通標的。 -/
def fixedApexConeFamily {K X : SSet.{u}} (p : K ⟶ X) (x : X.obj (Opposite.op ⦋0⦌)) :
    SSet.{u} := vertexFiber (coneFamilyApex p) x

/-- 概要：slice の頂点 fiber は内部 Hom の固定頂点の錐の模型へ標準的に写る。
方針：slice の比較の頂点との可換性で頂点 fiber の射を作る。
規約：充填性や同値性の追加仮定は射の定義に不要。
使われ方：Kerodon 4.6.6.8、7.5.4.6 の slice 側から共通模型への実際の比較。 -/
noncomputable def coneVertexFiberFamilyMap {K X : SSet.{u}} (p : K ⟶ X)
    (x : X.obj (Opposite.op ⦋0⦌)) :
    vertexFiber (sliceOverProjection p) x ⟶ fixedApexConeFamily p x :=
  vertexFiberMap (sliceOverProjection p) (coneFamilyApex p) (sliceConeFamilyMap p)
    (sliceConeFamilyMap_apex p) x

end SerrePositivity.InfinityCategories.HomotopyLimits
