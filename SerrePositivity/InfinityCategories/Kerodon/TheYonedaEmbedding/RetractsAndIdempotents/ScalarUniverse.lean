module
public import Mathlib.Algebra.Group.PUnit

public import Mathlib.Algebra.Group.WithOne.Basic

/-!
概要：元の二元冪等モノイドの宇宙変更を、恒等元と非恒等元を保つ同型として構成する。
方針：唯一の吸収元の値だけを持ち上げ、元の全乗法と逆写像を照合する。
規約：元の二元を同一視せず、単なる集合の濃度比較で代用しない。
使われ方：前層圏の小さい coherent 冪等図式の余極限。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の恒等と非恒等冪等元を保つ二元モノイドの宇宙変更。 -/
def walkingScalarUniverse : WithOne PUnit.{u + 1} →* WithOne PUnit.{v + 1} :=
  WithOne.mapMulHom { toFun := fun _ ↦ PUnit.unit, map_mul' := fun _ _ ↦ rfl }

/-- 元の宇宙変更の逆写像は、同じ二元を厳密に回収する。 -/
lemma walkingScalarUniverse_inverse (a : WithOne PUnit.{u + 1}) :
    walkingScalarUniverse.{v, u} (walkingScalarUniverse.{u, v} a) = a := by
  cases a using WithOne.recOneCoe with
  | one => rfl
  | coe a => cases a; rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
