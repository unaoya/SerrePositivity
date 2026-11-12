module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorHomPi

/-!
概要：小さい族の元の関手と全関手同型を全直積へまとめる。
方針：指定射影による後合成を成分とし、全 Hom の比較で可逆性を検査する。
規約：各点の同型族へ弱めず、元の全二胞体を保持する。
使われ方：小さい族の反映の全余単位。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の小さい族の関手の全直積。
方針：始域の各射影から指定関手へ合成する。
規約：元の各成分。使われ方：直積の反映関手と包含。 -/
def piSSetMap {ι : Type u} {C D : ι → SSet.{u + 1}} (f : ∀ i, C i ⟶ D i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetLift (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i ≫ f i)

/-- 概要：直積関手の元の指定成分。
方針：元の全直積を評価する。
規約：全射の等式。使われ方：直積の単位の成分計算。 -/
lemma piSSetMap_projection {ι : Type u} {C D : ι → SSet.{u + 1}}
    (f : ∀ i, C i ⟶ D i) (i : ι) :
    piSSetMap f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection D i = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i ≫ f i := rfl

/-- 概要：直積関手の合成は元の成分の合成。
方針：各次数で全成分を評価する。
規約：元の全射の等式。使われ方：反映の全余単位の比較。 -/
lemma piSSetMap_comp {ι : Type u} {C D E : ι → SSet.{u + 1}}
    (f : ∀ i, C i ⟶ D i) (g : ∀ i, D i ⟶ E i) :
    piSSetMap f ≫ piSSetMap g = piSSetMap (fun i ↦ f i ≫ g i) := rfl

/-- 概要：全成分の恒等関手の直積は元の恒等関手。
方針：各次数で全関数を評価する。
規約：厳密な等式。使われ方：直積の全同型。 -/
lemma piSSetMap_id {ι : Type u} (C : ι → SSet.{u + 1}) :
    piSSetMap (fun i ↦ 𝟙 (C i)) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C) := rfl

/-- 概要：全成分の指定全同型を元の直積値の全同型へまとめる。
方針：全 Hom 比較で順逆の二胞体を戻し、各成分で逆条件を検査する。
規約：同じ元の全関手を両端とする。
使われ方：直積の反映の全余単位の構成。 -/
def functorIsoOfPiComponents {ι : Type u} {T : SSet.{u + 1}}
    {C : ι → SSet.{u + 1}} [∀ i, Quasicategory (C i)]
    {F G : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C}
    (e : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i) (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G where
  hom := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv F G).symm (fun i ↦ (e i).hom)
  inv := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv G F).symm (fun i ↦ (e i).inv)
  hom_inv_id := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv F F).injective
    funext i
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv_id, Equiv.apply_symm_apply]
    exact (e i).hom_inv_id
  inv_hom_id := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv G G).injective
    funext i
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv_id, Equiv.apply_symm_apply]
    exact (e i).inv_hom_id

/-- 概要：直積関手による後合成は全二胞体の成分比較と可換。
方針：元の二胞体の辺の代表で全成分を計算する。
規約：元の全パラメーターを保持する。
使われ方：直積の単位 Hom 比較の成分計算。 -/
lemma functorHomPiEquiv_postcomp {ι : Type u} {T : SSet.{u + 1}}
    {C D : ι → SSet.{u + 1}} [∀ i, Quasicategory (C i)] [∀ i, Quasicategory (D i)]
    (f : ∀ i, C i ⟶ D i) {F G : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) (i : ι) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv (F ≫ piSSetMap f) (G ≫ piSSetMap f)
        ((hoFunctor.map ((ihom T).map (piSSetMap f))).toFunctor.map α) i =
      (hoFunctor.map ((ihom T).map (f i))).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv F G α i) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv_apply]
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ α
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
