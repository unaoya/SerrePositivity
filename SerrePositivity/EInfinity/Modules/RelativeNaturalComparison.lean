module

public import SerrePositivity.EInfinity.Modules.RelativeCylinderLaws
public import SerrePositivity.EInfinity.SimplicialLocalization.NerveFunctor
public import Mathlib.Tactic.FinCases

/-!
# 同じ弱自然変換から局所化の全関手間の可逆比較へ

概要：HA §1.3.4 の同じ係数自然変換を円筒の関手として局所化する。
方針：同じ円筒の射影が同値であることから両端点を比較する。
規約：比較は全関手単体集合のホモトピー圏の同型である。
使われ方：BE 底の同じ包含・置換の単位・余単位の回収。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.EInfinity.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

variable (C : RelativeCategory.{u})

/-- 概要：同じ円筒の両端点の全関手間の比較（HA §1.3.4）。
方針：同じ射影の逆と、端点・射影の厳密な合成則を使う。
規約：頂点ごとの比較に弱めない。使われ方：弱自然変換の局所化。 -/
def relativeCylinderEndpointIso :
    FunctorIso (localizationNerveMap (relativeCylinderEndpoint C 0))
      (localizationNerveMap (relativeCylinderEndpoint C 1)) := by
  let e := (relativeCylinderProjection_isQCatEquivalence C).choose
  have h (i : Fin 2) : FunctorIso e.inv (localizationNerveMap (relativeCylinderEndpoint C i)) := by
    have h := e.homInvIso.precomp (localizationNerveMap (relativeCylinderEndpoint C i))
    change FunctorIso
      (localizationNerveMap (relativeCylinderEndpoint C i) ≫
        (localizationNerveMap (relativeCylinderProjection C) ≫ e.inv))
      (localizationNerveMap (relativeCylinderEndpoint C i) ≫ 𝟙 _) at h
    simpa only [← Category.assoc, ← localizationNerveMap_comp,
      relativeCylinderEndpoint_projection, localizationNerveMap_id,
      Category.id_comp, Category.comp_id] using h
  exact (h 0).symm ≪≫ h 1

variable {C} {D : RelativeCategory.{u}} {F G : C ⟶ D}

/-- 概要：同じ弱自然変換の円筒関手は相対関手（HA §1.3.4）。
方針：通常の自然変換の uncurrying と指定弱射の合成閉性を使う。
規約：元の変換をそのまま使う。使われ方：全 nerve の比較の実関手。 -/
def relativeNaturalCylinder (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) : relativeCylinder C ⟶ D where
  functor := Functor.uncurry.obj (ComposableArrows.mk₁ η)
  map := by
    rintro ⟨i, X⟩ ⟨j, Y⟩ f hf
    fin_cases i <;> fin_cases j
    · change D.weakEquivalences (𝟙 _ ≫ F.functor.map f.2)
      rw [Category.id_comp]
      exact F.map f.2 hf
    · change D.weakEquivalences (η.app X ≫ G.functor.map f.2)
      exact D.weakEquivalences.comp_mem _ _ (hη X) (G.map f.2 hf)
    · have h := leOfHom f.1
      norm_num at h
    · change D.weakEquivalences (𝟙 _ ≫ G.functor.map f.2)
      rw [Category.id_comp]
      exact G.map f.2 hf

/-- 概要：同じ自然変換の円筒の零端点は元の関手（HA §1.3.4）。
方針：元の uncurrying の零端点で計算する。
規約：相対関手の厳密な等式。使われ方：比較の始域の回収。 -/
lemma relativeNaturalCylinder_zero (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) :
    relativeCylinderEndpoint C 0 ≫ relativeNaturalCylinder η hη = F := by
  apply relativeFunctor_ext
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change 𝟙 _ ≫ F.functor.map f = F.functor.map f
  exact Category.id_comp _

/-- 概要：同じ自然変換の円筒の一端点は元の関手（HA §1.3.4）。
方針：元の uncurrying の一端点で計算する。
規約：相対関手の厳密な等式。使われ方：比較の終域の回収。 -/
lemma relativeNaturalCylinder_one (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) :
    relativeCylinderEndpoint C 1 ≫ relativeNaturalCylinder η hη = G := by
  apply relativeFunctor_ext
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change 𝟙 _ ≫ G.functor.map f = G.functor.map f
  exact Category.id_comp _

/-- 概要：同じ弱自然変換から元の全局所化関手間の可逆比較（HA §1.3.4）。
方針：円筒の両端点の全比較を同じ円筒関手で後合成する。
規約：全関手単体集合のホモトピー圏の同型。使われ方：同じ模型の単位・余単位。 -/
def localizationNerveMapIsoOfWeakNatTrans (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) :
    FunctorIso (localizationNerveMap F) (localizationNerveMap G) := by
  have h := (relativeCylinderEndpointIso C).postcomp (localizationNerveMap (relativeNaturalCylinder η hη))
  simpa only [← localizationNerveMap_comp, relativeNaturalCylinder_zero, relativeNaturalCylinder_one] using h

end SerrePositivity.EInfinity.Modules
