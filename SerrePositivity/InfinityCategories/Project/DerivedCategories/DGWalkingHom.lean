module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Evaluation

/-! # 一つの係数複体を生成辺とする自由 dg 圏

概要：二対象の間の一つの生成辺に任意の Hom 係数複体を置く。
方針：複体値 quiver の既存の自由 dg 圏を使い、元の対象宇宙へ二点型を上げる。
規約：係数の平坦性は要求しない。使われ方：閉前合成の全次数 prism の普遍係数。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
open scoped ZeroObject

/-- 二対象を元の対象宇宙に置く。 -/
abbrev DGWalkingHomVertex : Type v := ULift.{v} Bool

/-- 始点から終点への生成辺だけに係数複体を置く quiver。 -/
def dgWalkingHomQuiver (A : Type u) [CommRing A] (M : Complex A) :
    FreeDGCategory.ComplexQuiver A DGWalkingHomVertex.{v}
  | ⟨false⟩, ⟨true⟩ => M
  | _, _ => 0

/-- 任意の係数複体を一つの生成辺とする二対象の自由 dg 圏。 -/
def DGWalkingHom (A : Type u) [CommRing A] (M : Complex A) : Type v :=
  FreeDGCategory.Objects A DGWalkingHomVertex.{v} (dgWalkingHomQuiver A M)

instance dgWalkingHom_enrichment (A : Type u) [CommRing A] (M : Complex A) :
    DGCategory A (DGWalkingHom.{u, v} A M) :=
  FreeDGCategory.dgCategory A DGWalkingHomVertex (dgWalkingHomQuiver A M)

/-- 係数複体を持つ生成辺の始点。 -/
def dgWalkingHomSource (A : Type u) [CommRing A] (M : Complex A) :
    DGWalkingHom.{u, v} A M := ⟨false⟩

/-- 係数複体を持つ生成辺の終点。 -/
def dgWalkingHomTarget (A : Type u) [CommRing A] (M : Complex A) :
    DGWalkingHom.{u, v} A M := ⟨true⟩

/-- 係数複体から、自由 dg 圏の指定二対象の Hom への生成辺の包含。 -/
def dgWalkingHomGenerator (A : Type u) [CommRing A] (M : Complex A) :
    M ⟶ homObject A (DGWalkingHom.{u, v} A M)
      (dgWalkingHomSource A M) (dgWalkingHomTarget A M) :=
  FreeDGCategory.edgeInclusion A DGWalkingHomVertex (dgWalkingHomQuiver A M)
    ⟨false⟩ ⟨true⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
