module
public import SerrePositivity.InfinityCategories.Core.EquivalenceCylinderFunctorIso
public import SerrePositivity.InfinityCategories.Core.JoinTensorInterval
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness
/-!
概要：coslice 内の全族の関手同型を、同じ固定始点を持つ全 join 錐の関手同型へ移す。
方針：可逆円柱の全族を展開し、join の右因子の直積比較を使う。
規約：全錐の比較であり各脚だけの比較ではない。使われ方：右 Kan の標準錐の実極限性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
/-- 可逆円柱の端点と join の右因子の直積比較は、全図式で厳密に可換。 -/
lemma joinTensorRight_equivalenceEndpoint (A B : SSet.{u}) (b : Bool) :
    equivalenceCylinderEndpoint (join A B) b ≫ joinTensorRight A B equivalenceInterval =
      joinMap (𝟙 A) (equivalenceCylinderEndpoint B b) := by
  let p := stdSimplexZeroUnitIso.hom ≫ equivalenceIntervalPoint b
  have hf (K : SSet.{u}) : fst K (Δ[0] : SSet.{u}) ≫ equivalenceCylinderEndpoint K b =
      K ◁ p := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨k, t⟩
    rfl
  apply (cancel_epi (fst (join A B) (Δ[0] : SSet.{u}))).1
  rw [← Category.assoc, hf, joinTensorRight_parameter, ← hf B]
  have hc : joinMap (𝟙 A) (fst B (Δ[0] : SSet.{u}) ≫ equivalenceCylinderEndpoint B b) =
      joinMap (𝟙 A) (fst B (Δ[0] : SSet.{u})) ≫
        joinMap (𝟙 A) (equivalenceCylinderEndpoint B b) := by
    simpa only [Category.id_comp] using
      joinMap_comp (𝟙 A) (𝟙 A) (fst B (Δ[0] : SSet.{u})) (equivalenceCylinderEndpoint B b)
  rw [hc, ← Category.assoc, joinTensorRight_unit]
/-- coslice 内の同型な二つの全族は、全 join 錐の関手としても同型。 -/
lemma nonempty_functorIso_sliceUnderUncurry {A K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} {f g : A ⟶ sliceUnder p} (e : FunctorIso f g) :
    Nonempty (FunctorIso (sliceUnderUncurry f) (sliceUnderUncurry g)) := by
  obtain ⟨H, h₀, h₁⟩ := exists_equivalenceCylinder_extension_of_functorIso e
  let C := joinTensorRight K A equivalenceInterval ≫ sliceUnderUncurry H
  apply nonempty_functorIso_of_equivalenceCylinder_extension C
  · rw [← Category.assoc, joinTensorRight_equivalenceEndpoint,
      ← sliceUnderUncurry_precomp, h₀]
  · rw [← Category.assoc, joinTensorRight_equivalenceEndpoint,
      ← sliceUnderUncurry_precomp, h₁]
/-- 恒等 coslice 錐の定値全族を展開すると、元の同じ頂点の定値全錐になる。 -/
lemma sliceUnderUncurry_const_identity {X : SSet.{u}} (A : SSet.{u}) (x : X _⦋0⦌) :
    sliceUnderUncurry (SSet.const (X := A) (cosliceIdentityCone x)) = SSet.const x := by
  let k := SSet.const (X := A) (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))
  have h : SSet.const (X := A) (cosliceIdentityCone x) =
      k ≫ SSet.yonedaEquiv.symm (cosliceIdentityCone x) := by
    rw [SSet.yonedaEquiv_symm_zero (cosliceIdentityCone x), SSet.comp_const]
  rw [h, sliceUnderUncurry_precomp, sliceUnderUncurry_yoneda]
  exact SSet.comp_const _ _
end SerrePositivity.InfinityCategories
