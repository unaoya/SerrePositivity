module

public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
概要：Noether スキームの既存の成分と包含を、有限の全射的な族に束ねる。
方針：既約成分の有限性と各点の成分を使い、既存の閉部分スキーム構造を保つ。
規約：被約構造へ置き換えず、Mathlib の成分の構造を使う。
使われ方：C06 の一般の Noether スキームから既約な場合への帰着。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- Noether スキームの既約成分の添字。 -/
abbrev noetherianComponentIndex (X : Scheme.{u}) :=
  { Z : Set X // Z ∈ irreducibleComponents X }

/-- Noether スキームの既約成分の添字は有限。 -/
theorem noetherianComponentIndex_finite (X : Scheme.{u}) [IsNoetherian X] :
    Finite (noetherianComponentIndex X) :=
  (finite_irreducibleComponents_of_isNoetherian (X := X)).to_subtype

/-- 既存の既約成分の、nilpotent の情報を保つ閉部分スキーム。 -/
def noetherianComponentScheme (X : Scheme.{u}) [IsNoetherian X]
    (Z : noetherianComponentIndex X) : Scheme.{u} :=
  X.irreducibleComponent Z.val Z.property

/-- 既存の既約成分の閉包含。 -/
def noetherianComponentInclusion (X : Scheme.{u}) [IsNoetherian X]
    (Z : noetherianComponentIndex X) : noetherianComponentScheme X Z ⟶ X :=
  X.irreducibleComponentι Z.val Z.property

/-- 各成分の指定した包含は閉埋め込み。 -/
theorem isClosedImmersion_noetherianComponentInclusion (X : Scheme.{u}) [IsNoetherian X]
    (Z : noetherianComponentIndex X) : IsClosedImmersion (noetherianComponentInclusion X Z) :=
  inferInstanceAs (IsClosedImmersion (X.irreducibleComponentι Z.val Z.property))

/-- 各成分の指定したスキームは既約。 -/
theorem irreducibleSpace_noetherianComponentScheme (X : Scheme.{u}) [IsNoetherian X]
    (Z : noetherianComponentIndex X) : IrreducibleSpace (noetherianComponentScheme X Z) :=
  inferInstanceAs (IrreducibleSpace (X.irreducibleComponent Z.val Z.property))

/-- 各成分の指定したスキームは Noether。 -/
theorem isNoetherian_noetherianComponentScheme (X : Scheme.{u}) [IsNoetherian X]
    (Z : noetherianComponentIndex X) : IsNoetherian (noetherianComponentScheme X Z) := by
  haveI : IsClosedImmersion (noetherianComponentInclusion X Z) :=
    isClosedImmersion_noetherianComponentInclusion X Z
  haveI : CompactSpace (noetherianComponentScheme X Z) :=
    QuasiCompact.compactSpace_of_compactSpace (noetherianComponentInclusion X Z)
  letI : IsLocallyNoetherian (noetherianComponentScheme X Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (noetherianComponentInclusion X Z)
  exact ⟨⟩

/-- すべての点は指定した既存の成分の包含の像に入る。 -/
theorem noetherianComponentInclusion_jointly_surjective (X : Scheme.{u}) [IsNoetherian X]
    (x : X) : ∃ (Z : noetherianComponentIndex X) (y : noetherianComponentScheme X Z),
      noetherianComponentInclusion X Z y = x := by
  let Z : noetherianComponentIndex X :=
    ⟨_root_.irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  exact ⟨Z, ⟨x, mem_irreducibleComponent⟩, rfl⟩

end SerrePositivity.AlgebraicGeometry
