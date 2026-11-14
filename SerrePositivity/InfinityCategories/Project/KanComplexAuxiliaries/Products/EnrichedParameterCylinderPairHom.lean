module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedParameterCylinderPoint

/-!
概要：二対象の円柱のパラメータと元の圏の Hom を組み合わせる射。
方針：端をまたぐ場合だけパラメータとの積を取り、逆向きは空 Hom を使う。
規約：単位・合成と整合する二つの写像族に適用する。
使われ方：豊穣関手と coherent nerve の pairing。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.EnrichedParameterCylinder
end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder

/-- 小さい円柱の Hom のパラメータを、指定した Hom の族と組み合わせる。 -/
def pairBySide (A : SSet.{u}) : (s t : Bool) → {U H : SSet.{u}} →
    (U ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.homBySide A s t (𝟙_ SSet.{u})) → (U ⟶ H) → (U ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.homBySide A s t H)
  | false, false, _, _, _, f => f
  | false, true, _, _, k, f => lift (k ≫ fst A (𝟙_ SSet.{u})) f
  | true, false, _, _, k, _ => k
  | true, true, _, _, _, f => f

/-- 同じ端での恒等族の pairing は元の恒等族そのもの。 -/
lemma pairBySide_identity (A H : SSet.{u}) (s : Bool)
    (k : 𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.homBySide A s s (𝟙_ SSet.{u})) (f : 𝟙_ SSet.{u} ⟶ H) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide A s s k f = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.identityBySide A H f s := by
  cases s <;> rfl

/-- pairing はパラメータ族の源の前合成と厳密に可換。 -/
lemma pairBySide_precomp (A : SSet.{u}) (s t : Bool) {U V H : SSet.{u}}
    (i : V ⟶ U) (k : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.homBySide A s t (𝟙_ SSet.{u})) (f : U ⟶ H) :
    i ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide A s t k f = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide A s t (i ≫ k) (i ≫ f) := by
  cases s <;> cases t
  all_goals
    apply SSet.hom_ext
    intro d
    rfl

/-- 合成と整合する二つの写像族の pairing も合成と整合する。 -/
lemma pairBySide_comp (A : SSet.{u}) (s t r : Bool) {U V W H K L : SSet.{u}}
    (m : U ⊗ V ⟶ W) (n : H ⊗ K ⟶ L)
    (a : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.homBySide A s t (𝟙_ SSet.{u}))
    (b : V ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.homBySide A t r (𝟙_ SSet.{u}))
    (c : W ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.homBySide A s r (𝟙_ SSet.{u}))
    (f : U ⟶ H) (g : V ⟶ K) (h : W ⟶ L)
    (hp : m ≫ c = (a ⊗ₘ b) ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.compositionBySide A (fst _ _) s t r)
    (hh : m ≫ h = (f ⊗ₘ g) ≫ n) :
    m ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide A s r c h =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide A s t a f ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide A t r b g) ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.compositionBySide A n s t r := by
  cases s <;> cases t <;> cases r
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨x, y⟩
    let xy : (U ⊗ V).obj d := (x, y)
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app hh d) xy
  · have hp' := ConcreteCategory.congr_hom (NatTrans.congr_app hp d) xy
    have hh' := ConcreteCategory.congr_hom (NatTrans.congr_app hh d) xy
    have hp₁ := congrArg (fun p : (A ⊗ (𝟙_ SSet.{u})).obj d ↦ p.1) hp'
    exact Prod.ext hp₁ hh'
  · exact (b.app d y).elim
  · have hp' := ConcreteCategory.congr_hom (NatTrans.congr_app hp d) xy
    have hh' := ConcreteCategory.congr_hom (NatTrans.congr_app hh d) xy
    have hp₁ := congrArg (fun p : (A ⊗ (𝟙_ SSet.{u})).obj d ↦ p.1) hp'
    exact Prod.ext hp₁ hh'
  · exact (a.app d x).elim
  · exact (a.app d x).elim
  · exact (b.app d y).elim
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app hh d) xy

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pairBySide := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pairBySide_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pairBySide_identity := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide_identity

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pairBySide_precomp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide_precomp

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide.match_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pairBySide.match_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide.match_1
