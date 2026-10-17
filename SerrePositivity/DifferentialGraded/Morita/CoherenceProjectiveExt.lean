module
public import SerrePositivity.DifferentialGraded.Morita.KernelResolutionModel

/-! # 射影入力上での主導来自然変換の一致判定

## 概要
主導来入力の自然変換は、射影的な通常入力の局所化像での成分から判定できる。

## 方針
標準射影解像度の増大は主局所化で同型であり、その自然性squareで成分を運ぶ。

## 規約と注意
終域は任意圏。dg圏の分解・局所Hom K-flat性を要求しない。

## 使われ方
U16aの単位・結合coherenceを同じ射影入力モデルへ帰着する。
-/
@[expose] public section
noncomputable section
universe u v w w'
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  {C : Type w} [Category.{w'} C]

/-- 主導来自然変換の成分は射影的通常入力だけで判定できる。 -/
lemma kernelActionNatTrans_ext_projective {F G : DerivedModuleCategory A D ⥤ C} {α β : F ⟶ G}
    (h : ∀ M : ModuleCategory A D, moduleHomotopicallyProjective A D M →
      α.app ((moduleToDerived A D).obj M) = β.app ((moduleToDerived A D).obj M)) : α = β := by
  apply moduleDerivedNatTrans_ext A D
  intro M
  let R := moduleCanonicalProjectiveResolution A D M
  have := moduleToDerived_inverts A D R.π R.quasiIso
  apply (cancel_epi (F.map ((moduleToDerived A D).map R.π))).1
  rw [α.naturality, β.naturality, h R.obj R.projective]

end SerrePositivity.DifferentialGraded.Morita
