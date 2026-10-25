module

public import SerrePositivity.InfinityCategories.F2.Presentable.PiFunctorMap

/-!
概要：小さい全直積の反映の全余単位と同値の全逆データを構成する。
方針：元の各成分の全同型を射影に沿って前合成し、全二胞体としてまとめる。
規約：元の全同値と反映のデータを保持する。
使われ方：小さい積の presentable 性の反映と同値移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：各反映の全余単位同型から直積の全余単位同型を構成する。
方針：元の各同型を元の直積の各射影に沿って制限する。
規約：随伴関手定理を使わない。
使われ方：直積反映の像の accessibility。 -/
def piReflectionCounitIso {ι : Type u} {C D : ι → SSet.{u + 1}}
    [∀ i, Quasicategory (D i)] {L : ∀ i, C i ⟶ D i} {R : ∀ i, D i ⟶ C i}
    (e : ∀ i, FunctorIso (R i ≫ L i) (𝟙 (D i))) :
    FunctorIso (piSSetMap R ≫ piSSetMap L) (𝟙 (piSSet D)) := by
  apply functorIsoOfPiComponents
  intro i
  change FunctorIso (piSSetProjection D i ≫ R i ≫ L i) (piSSetProjection D i)
  simpa only [Category.assoc, Category.comp_id] using
    FunctorIso.precomp (e i) (piSSetProjection D i)

/-- 概要：小さい族の元の全同値の直積は全同値。
方針：両全関手と両側の全可逆二胞体を直積へまとめる。
規約：元の各同値の全逆データを使う。
使われ方：反映 Ind 模型の積から元の圏の積への移送。 -/
def qCatEquivalencePi {ι : Type u} {C D : ι → SSet.{u + 1}}
    [∀ i, Quasicategory (C i)] [∀ i, Quasicategory (D i)]
    (e : ∀ i, QCatEquivalence (C i) (D i)) : QCatEquivalence (piSSet C) (piSSet D) where
  hom := piSSetMap (fun i ↦ (e i).hom)
  inv := piSSetMap (fun i ↦ (e i).inv)
  homInvIso := piReflectionCounitIso (fun i ↦ (e i).homInvIso)
  invHomIso := piReflectionCounitIso (fun i ↦ (e i).invHomIso)

end SerrePositivity.InfinityCategories.F2.Presentable
