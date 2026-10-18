module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Triangulated.TStructure.TExact

/-!
概要：bounded below 右導来関手は標準 t 構造のコホモロジー下限を保存する。
方針：同じ下限を持つ injective 複体の実際の模型と、模型上の右導来比較同型を使う。
規約：関手の右完全性は仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン導来比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive]

/--
概要：bounded below 右導来関手は各整数のコホモロジー下限を保つ。
方針：同じ下限の injective 模型で計算し、模型上の右導来の比較同型を通じて移す。
規約：分解の存在は Mathlib の実際の構成から得る。
使われ方：TT §3、Toën §3.2 の切断と上側切断の比較。
-/
lemma rightDerivedPlus_isGE (K : DerivedCategory.Plus C) (n : ℤ) [K.IsGE n] :
    (F.rightDerivedFunctorPlus.obj K).IsGE n := by
  obtain ⟨J, hJ, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  let J₀ := (InjectiveObject.ι C).mapCochainComplexPlus.obj J
  have : J₀.obj.IsStrictlyGE n := by
    dsimp [J₀]
    infer_instance
  have : IsIso (F.rightDerivedFunctorPlusUnit.app J₀) := by
    change IsIso (F.rightDerivedFunctorPlusUnit.app ((InjectiveObject.ι C).mapCochainComplexPlus.obj J))
    infer_instance
  have : (F.mapCochainComplexPlus.obj J₀).obj.IsStrictlyGE n := by
    change CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (.up ℤ)).obj J₀.obj) n
    infer_instance
  have : ((F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).obj J₀).IsGE n := by
    apply (DerivedCategory.Plus.isGE_ι_obj_iff _ n).mp
    change (DerivedCategory.Q.obj ((F.mapCochainComplexPlus.obj J₀).obj)).IsGE n
    infer_instance
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso
    (asIso (F.rightDerivedFunctorPlusUnit.app J₀) ≪≫ F.rightDerivedFunctorPlus.mapIso e) n

/--
概要：bounded below 右導来関手は標準 t 構造について左 t 完全。
方針：全ての整数の下限の保存を t 構造の標準の性質へ束ねる。
規約：右 t 完全性は仮定・主張しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の bounded below 比較。
-/
instance rightDerivedPlus_leftTExact : F.rightDerivedFunctorPlus.LeftTExact
    DerivedCategory.Plus.TStructure.t DerivedCategory.Plus.TStructure.t := by
  apply Functor.LeftTExact.mk
  intro K _
  exact rightDerivedPlus_isGE F K 0

end SerrePositivity.KST.DerivedGeometry
