module
public import SerrePositivity.KST.SConstruction.SequenceCompatibilityTransport
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! # 全パラメータの指定適合円柱を列の射で前合成する
概要：元の構造射と段の射の二合成の間の全円柱を、指定した列の射で移す。
方針：同じ基点つき写像空間の前合成を後合成し、両端だけを列の可換式で照合する。
規約：元の実円柱・指定境界の辺を保持し、新たなホモトピーを選ばない。
使われ方：元の K prism の族を単射源へ移して BF 厳密化に渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の全適合円柱を、指定した列の射に沿って源だけ前合成する。 -/
def sequenceCompatibilityFamily_precompose {A B C : KanSequence.{u}}
    (p : KanSequence.Hom A B) (f : ∀ n, (B.level n).space ⟶ (C.level n).space) (n : ℕ)
    {U : SSet.{u}} (H : SSet.Homotopy
      (SSet.const (X := U) (familyVertex (B.sigma n ≫ f (n + 1))))
      (SSet.const (familyVertex (PointedSimplicialSet.circle.{u} ◁ f n ≫ C.sigma n)))) :
    SSet.Homotopy
      (SSet.const (X := U) (familyVertex (A.sigma n ≫ (p.app (n + 1) ≫ f (n + 1)))))
      (SSet.const (familyVertex
        (PointedSimplicialSet.circle.{u} ◁ (p.app n ≫ f n) ≫ C.sigma n))) := by
  let q := PointedSimplicialSet.circle.{u} ◁ p.app n
  let Z := (C.level (n + 1)).space
  let V := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre q Z)
  refine
    { h := V.h
      h₀ := V.h₀.trans ?_
      h₁ := V.h₁.trans ?_
      rel := V.rel }
  · rw [SSet.const_comp]
    apply congrArg SSet.const
    change (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed q Z).right.app _ (familyVertex (B.sigma n ≫ f (n + 1))) = _
    rw [familyVertex_pre]
    apply congrArg familyVertex
    change (PointedSimplicialSet.circle.{u} ◁ p.app n) ≫ (B.sigma n ≫ f (n + 1)) = _
    rw [← Category.assoc, p.comm n, Category.assoc]
  · rw [SSet.const_comp]
    apply congrArg SSet.const
    change (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed q Z).right.app _
      (familyVertex (PointedSimplicialSet.circle.{u} ◁ f n ≫ C.sigma n)) = _
    rw [familyVertex_pre]
    apply congrArg familyVertex
    change (PointedSimplicialSet.circle.{u} ◁ p.app n) ≫
      (PointedSimplicialSet.circle.{u} ◁ f n ≫ C.sigma n) = _
    rw [← Category.assoc, ← whiskerLeft_comp]

/-- 指定した列で源を移しても、元の全時刻の円柱をそのまま後合成している。 -/
lemma sequenceCompatibilityFamily_precompose_h {A B C : KanSequence.{u}}
    (p : KanSequence.Hom A B) (f : ∀ n, (B.level n).space ⟶ (C.level n).space) (n : ℕ)
    {U : SSet.{u}} (H : SSet.Homotopy
      (SSet.const (X := U) (familyVertex (B.sigma n ≫ f (n + 1))))
      (SSet.const (familyVertex (PointedSimplicialSet.circle.{u} ◁ f n ≫ C.sigma n)))) :
    (sequenceCompatibilityFamily_precompose p f n H).h =
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ p.app n)
        (C.level (n + 1)).space := rfl

/-- 元の指定適合辺の境界は、源の前合成後も同じ指定辺として保持される。 -/
lemma sequenceCompatibilityFamily_precompose_boundary {A B C : KanSequence.{u}}
    (p : KanSequence.Hom A B) (f : ∀ n, (B.level n).space ⟶ (C.level n).space) (n : ℕ)
    {T U : SSet.{u}} (j : T ⟶ U) (H : SSet.Homotopy
      (SSet.const (X := U) (familyVertex (B.sigma n ≫ f (n + 1))))
      (SSet.const (familyVertex (PointedSimplicialSet.circle.{u} ◁ f n ≫ C.sigma n))))
    (e : (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (B.level n).space) (C.level (n + 1)).space).right.Edge
      (familyVertex (B.sigma n ≫ f (n + 1)))
      (familyVertex (PointedSimplicialSet.circle.{u} ◁ f n ≫ C.sigma n)))
    (h : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      snd T (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm e.edge) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (sequenceCompatibilityFamily_precompose p f n H).h =
      snd T (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm
        (sequenceCompatibilityEdge_precompose p f n e).edge := by
  rw [sequenceCompatibilityFamily_precompose_h, ← Category.assoc, h, Category.assoc]
  change _ ≫ (SSet.yonedaEquiv.symm e.edge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre _ _) = _
  rw [SSet.yonedaEquiv_symm_comp]
  rfl

end SerrePositivity.KST.SConstruction
