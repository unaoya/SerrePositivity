module

public import SerrePositivity.InfinityCategories.F2.Presentable.FunctorPiIso
public import SerrePositivity.InfinityCategories.F2.Presentable.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful

/-!
概要：小さい全直積に値を取る全関手間の二胞体を全成分へ分解する。
方針：関手圏の厳密な積比較とホモトピー圏の全 Hom 比較を合成する。
規約：任意の全パラメーターを保持する。
使われ方：小さい族の全随伴の単位と三角恒等式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：直積値の全関手間の元の二胞体は全成分の二胞体の族と全単射。
方針：全関手圏の厳密な同型の充満忠実性と全直積の Hom 比較を使う。
規約：指定した元の両全関手を保持する。
使われ方：直積の全随伴の構成。 -/
def functorHomPiEquiv {ι : Type u} {T : SSet.{u + 1}} {C : ι → SSet.{u + 1}}
    [∀ i, Quasicategory (C i)] (F G : T ⟶ piSSet C) :
    FunctorHom F G ≃ ∀ i, FunctorHom (F ≫ piSSetProjection C i) (G ≫ piSSetProjection C i) := by
  let e := functorPiIso T C
  have hf := (qCatEquivalenceOfIso e).isQCatEquivalence.isFullyFaithful.toHoFullyFaithful
  exact hf.homEquiv.trans (piSSetHoHomEquiv _ _)

/-- 概要：全二胞体の成分比較は元の各射影による後合成。
方針：元の二胞体の一本の辺の代表で計算する。
規約：全パラメーターを保持する。使われ方：全自然性と合成の検証。 -/
lemma functorHomPiEquiv_apply {ι : Type u} {T : SSet.{u + 1}}
    {C : ι → SSet.{u + 1}} [∀ i, Quasicategory (C i)]
    {F G : T ⟶ piSSet C} (α : FunctorHom F G) (i : ι) :
    functorHomPiEquiv F G α i =
      (hoFunctor.map ((ihom T).map (piSSetProjection C i))).toFunctor.map α := by
  obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective _ _ α
  rfl

/-- 概要：元の全二胞体の合成は全成分で計算される。
方針：各後合成関手の合成保存を使う。
規約：全関手を保持する。使われ方：直積の三角恒等式。 -/
lemma functorHomPiEquiv_comp {ι : Type u} {T : SSet.{u + 1}}
    {C : ι → SSet.{u + 1}} [∀ i, Quasicategory (C i)]
    {F G H : T ⟶ piSSet C} (α : FunctorHom F G) (β : FunctorHom G H) (i : ι) :
    functorHomPiEquiv F H (α ≫ β) i =
      functorHomPiEquiv F G α i ≫ functorHomPiEquiv G H β i := by
  simp only [functorHomPiEquiv_apply, CategoryTheory.Functor.map_comp]

/-- 概要：恒等二胞体の全成分は元の恒等二胞体。
方針：各後合成関手の恒等保存を使う。
規約：元の全関手 F。使われ方：全同型の逆条件。 -/
lemma functorHomPiEquiv_id {ι : Type u} {T : SSet.{u + 1}}
    {C : ι → SSet.{u + 1}} [∀ i, Quasicategory (C i)]
    (F : T ⟶ piSSet C) (i : ι) : functorHomPiEquiv F F (𝟙 _) i = 𝟙 _ := by
  simp only [functorHomPiEquiv_apply, CategoryTheory.Functor.map_id]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable
