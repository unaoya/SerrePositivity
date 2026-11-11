module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # Sphere の余積の次数付き基底

概要：自由 sphere 表示を持つ複体は各次数で自由であり、微分は零である。
方針：評価は余積を保存し、加群の余積は直和と同型であることを使う。
規約：添字と係数環の宇宙は同じ。使われ方：filtration の各商の基底選択。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded
open scoped DirectSum ZeroObject
variable (S : Type u) [CommRing S]

/-- 概要：sphere の各次数の加群は自由である。
方針：その次数では係数環、それ以外では零加群であることを使う。
規約：sphere はコホモロジー次数に集中する。使われ方：sphere の直和の自由性。 -/
theorem sphere_degree_free (n k : ℤ) : Module.Free S ((complexSphere S n).X k) := by
  classical
  by_cases h : k = n
  · exact Module.Free.of_equiv' (inferInstance : Module.Free S S)
      (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) n (𝟙_ (ModuleCat S)) k h).toLinearEquiv.symm
  · letI := ModuleCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) n (𝟙_ (ModuleCat S)) k h)
    infer_instance

/-- 概要：sphere の余積は各次数で自由である。
方針：次数評価の余積保存と具体的な加群の直和同型を合成する。
規約：任意の添字族に成立。使われ方：自由商の基底を選ぶ。 -/
theorem sphereCoproduct_degree_free {I : Type u} (d : I → ℤ) (k : ℤ) :
    Module.Free S ((∐ (fun i => complexSphere S (d i))).X k) := by
  classical
  let ev := HomologicalComplex.eval (ModuleCat.{u} S) (.up ℤ) k
  let e := PreservesCoproduct.iso ev (fun i => complexSphere S (d i)) ≪≫
    ModuleCat.coprodIsoDirectSum (fun i => (complexSphere S (d i)).X k)
  let (i : I) : Module.Free S ((complexSphere S (d i)).X k) := sphere_degree_free S (d i) k
  have hf : Module.Free S (⨁ i, (complexSphere S (d i)).X k) :=
    Module.Free.of_basis (DFinsupp.basis (fun i =>
      Module.Free.chooseBasis S ((complexSphere S (d i)).X k)))
  exact Module.Free.of_equiv' hf e.toLinearEquiv.symm

/-- 概要：sphere の余積の微分は零である。
方針：次数評価された余積の各脚との合成を調べ、sphere の微分零を使う。
規約：任意の隣接次数に成立。使われ方：商の微分が零であること。 -/
theorem sphereCoproduct_d {I : Type u} (d : I → ℤ) (k : ℤ) :
    (∐ (fun i => complexSphere S (d i))).d k (k + 1) = 0 := by
  let ev := HomologicalComplex.eval (ModuleCat.{u} S) (.up ℤ) k
  apply (isColimitOfPreserves ev (coproductIsCoproduct (fun i => complexSphere S (d i)))).hom_ext
  intro i
  change (Sigma.ι (fun i => complexSphere S (d i)) i.as).f k ≫ _ = _ ≫ 0
  rw [HomologicalComplex.Hom.comm]
  change 0 ≫ _ = _ ≫ 0
  rw [zero_comp, comp_zero]

/-- 概要：一点加群の自由 sphere 表示は評価の次数ごとの自由性を与える。
方針：通常の sphere 余積表示を次数評価し、自由性を移す。
規約：既存の表示をそのまま使う。使われ方：filtration の基底。 -/
theorem spherePresentation_degree_free {M : ModuleCategory S PUnit.{1}}
    (E : ModuleSphereFreePresentation S PUnit.{1} M) (k : ℤ) :
    Module.Free S (((ringModuleEquivalence S).functor.obj M).X k) := by
  exact Module.Free.of_equiv' (sphereCoproduct_degree_free S E.degree k)
    ((HomologicalComplex.eval (ModuleCat.{u} S) (.up ℤ) k).mapIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.spherePresentationEvaluationIso S E)).toLinearEquiv.symm

/-- 概要：一点加群の自由 sphere 表示の評価は微分零である。
方針：sphere 余積との鎖同型で微分零を移す。
規約：各整数次数で成立。使われ方：semibasis の微分下降条件。 -/
theorem spherePresentation_d {M : ModuleCategory S PUnit.{1}}
    (E : ModuleSphereFreePresentation S PUnit.{1} M) (k : ℤ) :
    ((ringModuleEquivalence S).functor.obj M).d k (k + 1) = 0 := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.spherePresentationEvaluationIso S E
  apply (cancel_mono (e.hom.f (k + 1))).1
  rw [zero_comp, ← HomologicalComplex.Hom.comm, sphereCoproduct_d, comp_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
