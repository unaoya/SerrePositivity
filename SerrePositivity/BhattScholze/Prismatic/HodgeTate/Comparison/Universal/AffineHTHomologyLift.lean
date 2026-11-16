module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.ProjectiveHomologyLift
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFormsProjective
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineCochainMap

/-!
# 元の標準 HT コホモロジー写像の複体上の実現

## 概要
元の完備形式からの標準 HT 写像を、同じ次数の single から元の affine 複体への射で実現する。

## 方針
元の形式の射影性を供給して、元のホモロジー射影に沿って持ち上げる。

## 規約
新しい同型を標準写像として選ばず、元の affineHTMap への一致を要求する。

## 使われ方
BS Proposition 6.2 の affine line の射 η の実現。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r i : ℕ)

/-- 元の標準 HT 写像は、元の完備形式の single からの複体の射で実現できる。 -/
theorem exists_affineHTSingleLift :
    ∃ q : (HomologicalComplex.single (ModuleCat.{u} (affineAlgebra P r)) (.up ℕ) i).obj
        (ModuleCat.of (affineAlgebra P r) (affineForms P r i)) ⟶ affineHTComplex P hP r,
      (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) i
        (ModuleCat.of (affineAlgebra P r) (affineForms P r i))).inv ≫
        HomologicalComplex.homologyMap q i = ModuleCat.ofHom (affineHTMap P hP r i) := by
  haveI := affineForms_projective P r i
  exact exists_single_homology_lift (affineHTComplex P hP r) i
    (ModuleCat.of (affineAlgebra P r) (affineForms P r i))
    (ModuleCat.ofHom (affineHTMap P hP r i))

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
