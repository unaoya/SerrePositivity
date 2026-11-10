module

public import SerrePositivity.InfinityCategories.F2.Presentable.PullbackCosliceEndpointComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.NativeCartesianFibrationPreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.CosliceBaseChangePreservation
public import SerrePositivity.InfinityCategories.F2.CatInfinity.QCatPullbackCone

/-!
概要：両成分と共通標的像の compact 性から、元の引き戻し内の対象の compact 性を導く。
方針：元の coslice を底変換した三成分の引き戻しで表し、全分類錐の filtered 保存性を使う。
規約：元の全共変 Hom と元の宇宙 u の添字を保持する。引き戻しの accessibility は仮定しない。
使われ方：引き戻しの小さい候補圏を compact 生成圏へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

local instance {E B D : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p] (G : D ⟶ B) :
    LeftFibration (pullback.snd p G) :=
  ⟨leftFibrations.pullback_snd p G (LeftFibration.mem (p := p))⟩

/-- 概要：元の引き戻しの両成分と共通標的像が μ-compact なら元の対象も μ-compact。
方針：元の coslice の全引き戻し表示と、同じ全分類図式の小さい filtered 保存判定を使う。
規約：一方の関手の inner fibration 性と元の射影の保存性を明示する。
使われ方：小さい候補族の引き戻し内での compact 性。 -/
lemma isKappaCompact_pullback_of_components
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (pullback.fst p q))
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (pullback.snd p q))
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ p) (v : (pullback p q) _⦋0⦌)
    (he : Compact.IsKappaCompact.{u, u + 1} μ ((pullback.fst p q).app _ v))
    (hd : Compact.IsKappaCompact.{u, u + 1} μ ((pullback.snd p q).app _ v))
    (hb : Compact.IsKappaCompact.{u, u + 1} μ (p.app _ ((pullback.fst p q).app _ v))) :
    Compact.IsKappaCompact.{u, u + 1} μ v := by
  let a := SSet.yonedaEquiv.symm v
  let e := pullback.snd (sliceUnderProjection (a ≫ pullback.fst p q)) (pullback.fst p q)
  let d := pullback.snd (sliceUnderProjection (a ≫ pullback.snd p q)) (pullback.snd p q)
  let b := pullback.snd (sliceUnderProjection ((a ≫ pullback.fst p q) ≫ p)) (pullback.fst p q ≫ p)
  have : LeftFibration (pullbackCosliceLeftMap p q a) := pullbackCosliceLeftMap_leftFibration p q a
  have he' := cosliceBaseChangeClassification_preservesKappaFilteredColimits
    (pullback.fst p q) v hf he
  have hd' := cosliceBaseChangeClassification_preservesKappaFilteredColimits
    (pullback.snd p q) v hs hd
  have hb' : Compact.PreservesKappaFilteredColimits.{u, u + 1} μ
      (leftStraighteningInfinityDiagram b) := by
    let Φ (z : (Δ[0] : SSet.{u + 1}) ⟶ B) : Prop :=
      Compact.PreservesKappaFilteredColimits.{u, u + 1} μ
        (leftStraighteningInfinityDiagram
          (pullback.snd (sliceUnderProjection z) (pullback.fst p q ≫ p)))
    apply (congrArg Φ (Category.assoc a (pullback.fst p q) p)).mpr
    exact cosliceBaseChangeClassification_preservesKappaFilteredColimits
      (pullback.fst p q ≫ p) v (hf.comp hp) hb
  have hc := cartesianFibrationClassification_preservesKappaFilteredColimits h
    (pullbackCosliceToLeft p q a) (pullbackCosliceToRight p q a)
    (pullbackCosliceLeftMap p q a) (pullbackCosliceRightMap p q a)
    (pullbackCosliceBaseChange_isPullback p q a)
    (sliceUnderProjection a) e d b
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
    he' hd' hb'
  exact hc.of_functorIso (Compact.covariantRepresentableInfinity_cosliceIso v).symm

end SerrePositivity.InfinityCategories.F2.Presentable
